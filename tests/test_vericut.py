"""End-to-end tests of the `vericut` binary, with the reference `flac` tool as the oracle.

  * our FLAC output decodes bit-exact with `flac -d` (which also checks CRCs);
  * our decoder reads `flac`-made files bit-exact;
  * our own round trip is the identity;
  * `export` gives exactly the concatenated half-open sample ranges;
  * every headline theorem uses only the standard axioms.

Real clips in samples/audio/ (not committed) are used when present.

Run:  python3 tests/test_vericut.py            (from the project root)
Env:  VERICUT_BIN  path to the binary (default core/.lake/build/bin/vericut)
      FLAC         path to the reference flac (default flac)
      AUDIO_DIR    real clips (default samples/audio, or ../verified-cut/samples/audio)
      LONG=1       also run the long clips (the podcast)
"""
import json, os, random, struct, subprocess, sys, tempfile, unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("VERICUT_BIN", os.path.join(ROOT, "core/.lake/build/bin/vericut"))
FLAC = os.environ.get("FLAC", "flac")
AUDIO = os.environ.get("AUDIO_DIR") or next(
    (d for d in [os.path.join(ROOT, "samples/audio"), os.path.join(ROOT, "../verified-cut/samples/audio")]
     if os.path.isdir(d)), None)
LONG = os.environ.get("LONG") == "1"
TMP = tempfile.mkdtemp(prefix="vericut-test-")


def run(args, check=True, cwd=None):
    p = subprocess.run(args, capture_output=True, cwd=cwd)
    if check and p.returncode != 0:
        raise AssertionError(f"{args} failed ({p.returncode}): {p.stderr.decode().strip()}")
    return p


def vericut(*args, check=True):
    p = run([BIN, *args], check=check)
    return json.loads(p.stdout) if p.returncode == 0 else p


def tmp(name):
    return os.path.join(TMP, name)


def pack(samples, bits):
    """Little-endian signed bytes, as WAV and `flac --force-raw-format` use (8-bit: unsigned)."""
    width = (bits + 7) // 8
    if width == 1:
        return bytes((s + 128) & 0xFF for s in samples)
    shift = 8 * width - bits
    return b"".join(((s << shift) & ((1 << (8 * width)) - 1)).to_bytes(width, "little") for s in samples)


def write_wav(path, samples, rate, channels, bits):
    data = pack(samples, bits)
    width = (bits + 7) // 8
    hdr = b"RIFF" + struct.pack("<I", 36 + len(data)) + b"WAVEfmt " + struct.pack(
        "<IHHIIHH", 16, 1, channels, rate, rate * channels * width, channels * width, 8 * width)
    with open(path, "wb") as f:
        f.write(hdr + b"data" + struct.pack("<I", len(data)) + data)


def wav_data(path):
    """The data chunk of a WAV file (ours writes format 1)."""
    with open(path, "rb") as f:
        d = f.read()
    i = 12
    while i + 8 <= len(d):
        tag, size = d[i:i + 4], struct.unpack("<I", d[i + 4:i + 8])[0]
        if tag == b"data":
            return d[i + 8:i + 8 + size]
        i += 8 + size + size % 2
    raise AssertionError("no data chunk")


def flac_decode_raw(path, bits):
    out = path + ".raw"
    run([FLAC, "-d", "-s", "-f", "--force-raw-format", "--endian=little", "--sign=signed", "-o", out, path])
    with open(out, "rb") as f:
        raw = f.read()
    return raw


def raw_of(samples, bits):
    # flac's raw output is signed even for 8-bit, and not left-justified
    width = (bits + 7) // 8
    return b"".join((s & ((1 << (8 * width)) - 1)).to_bytes(width, "little") for s in samples)


def synth(kind, n, channels, bits, seed=0):
    rnd = random.Random(seed)
    lo, hi = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
    out = []
    for i in range(n):
        for c in range(channels):
            if kind == "silence":
                v = 0
            elif kind == "dc":
                v = hi // 3
            elif kind == "noise":
                v = rnd.randint(lo, hi)
            elif kind == "extremes":
                v = lo if (i + c) % 2 else hi
            elif kind == "tone":
                import math
                v = int(hi * 0.8 * math.sin(2 * math.pi * (220 + 110 * c) * i / 44100))
            elif kind == "wasted":  # low 3 bits always zero
                v = (rnd.randint(lo, hi) >> 3) << 3
            elif kind == "steps":  # mostly constant blocks with a few jumps
                v = ((i // 3000) * 1234 + c * 77) % hi
            elif kind == "chirp":  # three sweeping partials and a little noise
                import math
                t = i / 44100
                v = int(hi * 0.25 * (math.sin(2 * math.pi * (200 + 800 * t) * t) + math.sin(2 * math.pi * (1500 + 300 * c) * t)
                                     + 0.5 * math.sin(2 * math.pi * 5000 * t)) + rnd.randint(-40, 40))
            out.append(v)
    return out


CASES = [
    # kind, frames, channels, bits, rate
    ("silence", 5000, 2, 16, 44100),
    ("dc", 5000, 1, 16, 44100),
    ("tone", 20000, 2, 16, 44100),
    ("noise", 9000, 2, 16, 48000),
    ("noise", 4097, 1, 24, 96000),
    ("extremes", 3000, 2, 24, 44100),
    ("tone", 7000, 2, 24, 44100),
    ("wasted", 6000, 2, 16, 44100),
    ("steps", 10000, 2, 16, 44100),
    ("noise", 3000, 6, 16, 48000),
    ("tone", 2000, 8, 16, 32000),
    ("noise", 2000, 1, 8, 8000),
    ("tone", 2000, 2, 8, 22050),
    ("tone", 1, 2, 16, 44100),
    ("noise", 15, 1, 16, 44100),
    ("noise", 17, 2, 16, 44100),
    ("tone", 5000, 2, 16, 12345),  # rate with no frame header code
    ("silence", 0, 2, 16, 44100),
    ("tone", 3000, 2, 32, 48000),
    ("noise", 2000, 1, 32, 48000),
    ("chirp", 30000, 2, 16, 44100),  # wants high-order linear prediction
]


class Synthetic(unittest.TestCase):
    def check_case(self, kind, n, ch, bits, rate, levels=(0, 5, 8)):
        samples = synth(kind, n, ch, bits)
        name = f"{kind}_{n}_{ch}ch_{bits}b_{rate}"
        wav = tmp(name + ".wav")
        write_wav(wav, samples, rate, ch, bits)
        info = vericut("probe", wav)
        self.assertEqual(info, {"sampleRate": rate, "channels": ch, "bitsPerSample": bits,
                                "samples": n, "format": "wav"})
        for level in levels:
            out = tmp(f"{name}.l{level}.flac")
            res = vericut("encode", wav, out, "--level", str(level))
            self.assertEqual(res["samples"], n)
            self.assertEqual(res["bytes"], os.path.getsize(out))
            # reference decoder (checks both CRCs and the stream structure)
            self.assertEqual(flac_decode_raw(out, bits), raw_of(samples, bits), f"flac -d of {out}")
            # our round trip
            back = tmp(f"{name}.l{level}.back.wav")
            vericut("decode", out, back)
            self.assertEqual(wav_data(back), pack(samples, bits), f"our decode of {out}")
            self.assertEqual(vericut("probe", out)["samples"], n)
        # our decoder on the reference encoder's output, at its fastest and slowest settings
        for level in (0, 8):
            ref = tmp(f"{name}.ref{level}.flac")
            raw = tmp(f"{name}.raw")
            with open(raw, "wb") as f:
                f.write(raw_of(samples, bits))
            run([FLAC, "-s", "-f", f"-{level}", "--force-raw-format", "--endian=little", "--sign=signed",
                 f"--channels={ch}", f"--bps={bits}", f"--sample-rate={rate}", "-o", ref, raw])
            back = tmp(f"{name}.ref{level}.wav")
            vericut("decode", ref, back)
            self.assertEqual(wav_data(back), pack(samples, bits), f"our decode of flac -{level}")


for case in CASES:
    def test(self, case=case):
        self.check_case(*case)
    setattr(Synthetic, "test_" + "_".join(map(str, case)), test)


def real_clips():
    if not AUDIO:
        return []
    names = sorted(f for f in os.listdir(AUDIO) if f.endswith(".wav") and not f.endswith(".orig.wav"))
    return [os.path.join(AUDIO, f) for f in names if LONG or os.path.getsize(os.path.join(AUDIO, f)) < 100_000_000]


def subframe_types(path):
    """Counts of subframe types in a FLAC file, from `flac --analyze`."""
    ana = tmp(os.path.basename(path) + ".ana")
    run([FLAC, "-s", "-f", "-a", "-o", ana, path])
    counts = {}
    with open(ana) as f:
        for line in f:
            for word in line.split():
                if word.startswith("type="):
                    counts[word[5:]] = counts.get(word[5:], 0) + 1
    return counts


class Lpc(unittest.TestCase):
    """Linear prediction: used from level 3 on, never at 0-2, smaller than fixed predictors,
    and every candidate decodes bit-exact (the synthetic cases check that at each level)."""

    def test_levels(self):
        samples = synth("chirp", 30000, 2, 16)
        wav = tmp("lpc_chirp.wav")
        write_wav(wav, samples, 44100, 2, 16)
        sizes = {}
        for level in (0, 2, 3, 5, 8):
            out = tmp(f"lpc_chirp.l{level}.flac")
            vericut("encode", wav, out, "--level", str(level))
            types = subframe_types(out)
            if level < 3:
                self.assertNotIn("LPC", types, f"level {level}")
            else:
                self.assertGreater(types.get("LPC", 0), 0, f"level {level}")
            self.assertEqual(flac_decode_raw(out, 16), raw_of(samples, 16))
            sizes[level] = os.path.getsize(out)
        self.assertLess(sizes[5], sizes[2])
        self.assertLessEqual(sizes[8], sizes[5])

    def test_close_to_libflac(self):
        # within 1% of libFLAC's size at -5 and -8 on a signal LPC is made for
        samples = synth("chirp", 60000, 2, 16, seed=1)
        wav = tmp("lpc_chirp2.wav")
        write_wav(wav, samples, 44100, 2, 16)
        for level in (5, 8):
            ours, ref = tmp(f"lpc2.l{level}.flac"), tmp(f"lpc2.ref{level}.flac")
            vericut("encode", wav, ours, "--level", str(level))
            run([FLAC, "-s", "-f", f"-{level}", "-o", ref, wav])
            self.assertLess(os.path.getsize(ours), os.path.getsize(ref) * 1.01, f"level {level}")


class RealClips(unittest.TestCase):
    def test_clips(self):
        clips = real_clips()
        if not clips:
            self.skipTest("no clips in samples/audio")
        for wav in clips:
            with self.subTest(clip=os.path.basename(wav)):
                out = tmp(os.path.basename(wav) + ".flac")
                vericut("encode", wav, out)
                info = vericut("probe", wav)
                self.assertEqual(flac_decode_raw(out, info["bitsPerSample"]), wav_data(wav))
                ref = tmp(os.path.basename(wav) + ".ref.flac")
                run([FLAC, "-s", "-f", "-8", "-o", ref, wav])
                back = tmp(os.path.basename(wav) + ".back.wav")
                vericut("decode", ref, back)
                self.assertEqual(wav_data(back), wav_data(wav))


class Export(unittest.TestCase):
    def setUp(self):
        self.a = synth("tone", 30000, 2, 16)
        self.b = synth("noise", 20000, 2, 16, seed=7)
        self.wa, self.wb = tmp("exp_a.wav"), tmp("exp_b.flac")
        write_wav(self.wa, self.a, 44100, 2, 16)
        write_wav(tmp("exp_b.wav"), self.b, 44100, 2, 16)
        run([FLAC, "-s", "-f", "-5", "-o", self.wb, tmp("exp_b.wav")])  # sources may be FLAC too

    def export(self, clips, level=5):
        t = tmp("timeline.json")
        with open(t, "w") as f:
            json.dump({"clips": [{"src": s, "in": i, "out": o} for s, i, o in clips]}, f)
        out = tmp("export.flac")
        return vericut("export", t, out, "--level", str(level), check=False), out

    def test_splice(self):
        clips = [(self.wa, 100, 5000), (self.wb, 0, 1), (self.wa, 4096, 4096), (self.wb, 19000, 20000),
                 (self.wa, 0, 30000), (self.wb, 333, 7777)]
        want = []
        for src, i, o in clips:
            s = self.a if src == self.wa else self.b
            want += s[2 * i:2 * o]
        for level in (0, 8):
            res, out = self.export(clips, level)
            self.assertIsInstance(res, dict, getattr(res, "stderr", b"").decode())
            self.assertEqual(res["samples"], len(want) // 2)
            self.assertEqual(res["bytes"], os.path.getsize(out))
            self.assertEqual(flac_decode_raw(out, 16), raw_of(want, 16))

    def test_rejects(self):
        mono = tmp("exp_mono.wav")
        write_wav(mono, synth("tone", 1000, 1, 16), 44100, 1, 16)
        for clips, msg in [([(self.wa, 0, 30001)], b"outside"), ([(self.wa, 10, 5)], b"outside"),
                           ([(self.wa, 0, 10), (mono, 0, 10)], b"formats differ"), ([], b"no clips"),
                           ([(tmp("missing.wav"), 0, 1)], b"")]:
            res, _ = self.export(clips)
            self.assertNotIsInstance(res, dict)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn(msg, res.stderr)


def write_wav_extensible(path, samples, rate, channels, bits, container=None):
    """WAVE_FORMAT_EXTENSIBLE with the PCM subformat, as ffmpeg writes 24-bit and multichannel files."""
    width = container or (bits + 7) // 8
    shift = 8 * width - bits
    data = b"".join(((s << shift) & ((1 << (8 * width)) - 1)).to_bytes(width, "little") for s in samples)
    guid = bytes([1, 0, 0, 0, 0, 0, 0x10, 0, 0x80, 0, 0, 0xAA, 0, 0x38, 0x9B, 0x71])
    fmt = struct.pack("<HHIIHHHHI", 0xFFFE, channels, rate, rate * channels * width, channels * width,
                      8 * width, 22, bits, 0) + guid
    body = b"WAVE" + b"fmt " + struct.pack("<I", len(fmt)) + fmt + b"LIST" + struct.pack("<I", 4) + b"INFO" \
        + b"data" + struct.pack("<I", len(data)) + data
    with open(path, "wb") as f:
        f.write(b"RIFF" + struct.pack("<I", len(body)) + body)


class WavInput(unittest.TestCase):
    """What the app relies on: plain and extensible PCM WAVs load; anything else makes `probe` fail."""

    def test_extensible_24bit(self):
        samples = synth("tone", 3000, 2, 24)
        w = tmp("ext24.wav")
        write_wav_extensible(w, samples, 48000, 2, 24)
        self.assertEqual(vericut("probe", w), {"sampleRate": 48000, "channels": 2, "bitsPerSample": 24,
                                               "samples": 3000, "format": "wav"})
        out = tmp("ext24.flac")
        vericut("encode", w, out)
        self.assertEqual(flac_decode_raw(out, 24), raw_of(samples, 24))

    def test_ffmpeg_written(self):
        for codec, bits in [("pcm_s16le", 16), ("pcm_s24le", 24)]:
            for ch in (1, 2, 6):
                with self.subTest(codec=codec, channels=ch):
                    w = tmp(f"ff_{codec}_{ch}.wav")
                    run(["ffmpeg", "-v", "error", "-y", "-f", "lavfi", "-i", "sine=frequency=440:duration=0.5",
                         "-ac", str(ch), "-ar", "44100", "-c:a", codec, w])
                    info = vericut("probe", w)
                    self.assertEqual((info["bitsPerSample"], info["channels"]), (bits, ch))
                    out = tmp(f"ff_{codec}_{ch}.flac")
                    vericut("encode", w, out)
                    raw = run(["ffmpeg", "-v", "error", "-i", w, "-f", codec[4:], "-"]).stdout
                    self.assertEqual(flac_decode_raw(out, bits), raw)

    def test_probe_rejects(self):
        cases = {
            "float": ["-c:a", "pcm_f32le"],
            "alaw": ["-c:a", "pcm_alaw"],
            "mp3": ["-c:a", "libmp3lame", "-f", "wav"],
        }
        for name, args in cases.items():
            with self.subTest(kind=name):
                w = tmp(f"bad_{name}.wav")
                p = run(["ffmpeg", "-v", "error", "-y", "-f", "lavfi", "-i", "sine=duration=0.2", *args, w],
                        check=False)
                if p.returncode != 0:
                    self.skipTest(f"ffmpeg can't write {name}")
                res = vericut("probe", w, check=False)
                self.assertNotIsInstance(res, dict)
                self.assertNotEqual(res.returncode, 0)
        many = tmp("bad_9ch.wav")
        write_wav_extensible(many, [0] * 90, 44100, 9, 16)
        self.assertNotEqual(vericut("probe", many, check=False).returncode, 0)


class Cli(unittest.TestCase):
    def test_peaks(self):
        s = [0, 0] * 50 + [16384, 16384] * 50 + [-32768, -32768] * 50
        w = tmp("peaks.wav")
        write_wav(w, s, 44100, 2, 16)
        p = vericut("peaks", w, "3")
        self.assertEqual(p, {"min": [0, 0, -1], "max": [0, 0.5, 0]})
        f = tmp("peaks.flac")
        vericut("encode", w, f)
        self.assertEqual(vericut("peaks", f, "3"), p)

    def test_peaks_wav_matches_flac(self):
        # WAV peaks read the bytes directly; FLAC peaks go through the decoder
        for bits in (8, 12, 16, 20, 24, 32):
            for ch in (1, 2, 3):
                with self.subTest(bits=bits, channels=ch):
                    w, f = tmp(f"pk{bits}_{ch}.wav"), tmp(f"pk{bits}_{ch}.flac")
                    write_wav(w, synth("noise", 3000, ch, bits), 44100, ch, bits)
                    vericut("encode", w, f)
                    self.assertEqual(vericut("peaks", w, "37"), vericut("peaks", f, "37"))

    def test_peaks_count(self):
        # the app asks for min(samples / 32, 100000) buckets; the count must be exact for any request
        w = tmp("peaks_count.wav")
        write_wav(w, synth("noise", 1000, 2, 16), 44100, 2, 16)
        for n in (0, 1, 7, 31, 1000, 1001, 4096, 100000):
            with self.subTest(buckets=n):
                p = vericut("peaks", w, str(n))
                self.assertEqual((len(p["min"]), len(p["max"])), (n, n))
                self.assertTrue(all(-1 <= a <= b <= 1 for a, b in zip(p["min"], p["max"])))

    def test_errors(self):
        bad = tmp("bad.wav")
        with open(bad, "wb") as f:
            f.write(b"not audio at all")
        p = vericut("probe", bad, check=False)
        self.assertNotEqual(p.returncode, 0)
        self.assertTrue(p.stderr)
        p = run([BIN, "frobnicate"], check=False)
        self.assertNotEqual(p.returncode, 0)


class ProofAudit(unittest.TestCase):
    def test_axioms(self):
        core = os.path.join(ROOT, "core")
        src = os.path.join(core, "VeriCut/Correctness.lean")
        if not os.path.exists(src):
            self.skipTest("no Correctness.lean")
        p = run(["lake", "env", "lean", src], check=False, cwd=core)
        out = (p.stdout + p.stderr).decode()
        self.assertEqual(p.returncode, 0, out)
        self.assertNotIn("sorry", out)
        # Correctness.lean pins each theorem's axioms with #guard_msgs; a change fails the build above.
        self.assertNotIn("error", out)


if __name__ == "__main__":
    unittest.main(verbosity=1)
