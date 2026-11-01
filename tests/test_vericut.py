"""End-to-end tests: the Lean `vericut` binary against ffmpeg as the oracle.

What "correct" means (mirrors the Lean spec, `core/VeriCut/Spec/Export.lean`):
  * the output has exactly the requested frames, in display order;
  * every frame the plan *copies* decodes bit-identically to the source frame
    (ffmpeg `framemd5` of decoded pictures), and its compressed packet is
    byte-identical (ffmpeg `-c copy -f framemd5`);
  * every re-encoded frame is close to the source (PSNR threshold), the
    `approx` relation of the encoder contract.

Run:  python3 tests/test_vericut.py            (from the project root)
Env:  VERICUT_BIN      path to the vericut binary (default core/.lake/build/bin/vericut)
      VERICUT_ENCODER  ffmpeg encoder for boundary frames (default libx264;
                        use h264_videotoolbox on a Mac for the hardware path)
      FFMPEG / FFPROBE  tool paths
"""
import array, fractions, json, math, os, shutil, struct, subprocess, sys, tempfile, unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("VERICUT_BIN", os.path.join(ROOT, "core/.lake/build/bin/vericut"))
ENCODER = os.environ.get("VERICUT_ENCODER", "libx264")
FFMPEG = os.environ.get("FFMPEG", "ffmpeg")
FFPROBE = os.environ.get("FFPROBE", "ffprobe")
SAMPLES = os.path.join(ROOT, "samples")
MIN_PSNR = 35.0


def sample(name):
    return os.path.join(SAMPLES, name)


# Same command as in samples/fetch_samples.sh. Generated, not committed.
OPEN_GOP = "gop24_open.mp4"
OPEN_GOP_ARGS = ["-f", "lavfi", "-i", "testsrc2=size=640x360:rate=30", "-t", "4", "-c:v", "libx264",
                 "-pix_fmt", "yuv420p", "-bf", "2",
                 "-x264-params", "keyint=24:min-keyint=24:scenecut=0:open-gop=1"]


# H.264 + AAC-LC with a non-periodic chirp, so a misaligned cut can't match by
# accident. Same size and rate as gop30_nob.mp4 (no audio), so they share a timeline.
# PNS is off: its noise bands are random in the decoder, so they never decode
# the same twice.
AV = "av_chirp.mp4"
AV_ARGS = ["-f", "lavfi", "-i", "testsrc2=size=640x360:rate=30", "-f", "lavfi", "-i",
           "aevalsrc=0.3*sin(2*PI*(200+300*t)*t)|0.3*sin(2*PI*(500+70*t*t)*t):s=48000",
           "-t", "6", "-c:v", "libx264", "-pix_fmt", "yuv420p", "-bf", "0",
           "-x264-params", "keyint=30:min-keyint=30:scenecut=0", "-c:a", "aac", "-aac_pns", "0", "-b:a", "128k"]


def setUpModule():
    if not os.path.exists(sample(OPEN_GOP)):
        run([FFMPEG, "-v", "error", "-y", *OPEN_GOP_ARGS, sample(OPEN_GOP)])
    if not os.path.exists(sample(AV)):
        run([FFMPEG, "-v", "error", "-y", *AV_ARGS, sample(AV)])


def run(args, check=True):
    p = subprocess.run(args, capture_output=True, text=True)
    if check and p.returncode != 0:
        raise AssertionError(f"{args[0]} failed ({p.returncode}): {p.stderr.strip()}")
    return p


def vericut(*args, check=True):
    return run([BIN, *args], check=check)


def probe(path):
    return json.loads(vericut("probe", path).stdout)


def decoded_hashes(path):
    """md5 of every decoded picture, in display order (edit lists ignored, as in the planner)."""
    out = run([FFMPEG, "-v", "error", "-ignore_editlist", "1", "-i", path, "-map", "0:v:0",
               "-f", "framemd5", "-"]).stdout
    return [l.split(",")[-1].strip() for l in out.splitlines() if l and not l.startswith("#")]


def packet_hashes(path):
    """md5 of every compressed packet, in decode order."""
    out = run([FFMPEG, "-v", "error", "-i", path, "-map", "0:v:0", "-c", "copy",
               "-f", "framemd5", "-"]).stdout
    return [l.split(",")[-1].strip() for l in out.splitlines() if l and not l.startswith("#")]


def idr_packets(path):
    """Per packet in decode order: does it contain an H.264 IDR slice (nal_unit_type 5)?"""
    log = run([FFMPEG, "-loglevel", "trace", "-i", path, "-map", "0:v:0", "-c", "copy",
               "-bsf:v", "trace_headers", "-f", "null", "-"]).stderr
    out = []
    for l in log.splitlines():
        if "[trace_headers" not in l:
            continue
        if "Packet:" in l:
            out.append(False)
        elif out and "nal_unit_type: 5(IDR)" in l:
            out[-1] = True
    return out


def raw_frames(path, w, h):
    raw = run_bytes([FFMPEG, "-v", "error", "-ignore_editlist", "1", "-i", path, "-map", "0:v:0",
                     "-f", "rawvideo", "-pix_fmt", "gray", "-"])
    n = w * h
    return [raw[i:i + n] for i in range(0, len(raw), n)]


def run_bytes(args):
    p = subprocess.run(args, capture_output=True)
    if p.returncode != 0:
        raise AssertionError(p.stderr.decode())
    return p.stdout


def psnr(a, b):
    sa, sb = a[::31], b[::31]
    mse = sum((x - y) ** 2 for x, y in zip(sa, sb)) / len(sa)
    return 99.0 if mse == 0 else 10 * math.log10(255 * 255 / mse)


def size_of(path):
    s = json.loads(run([FFPROBE, "-v", "error", "-select_streams", "v:0", "-show_entries",
                        "stream=width,height", "-of", "json", path]).stdout)["streams"][0]
    return s["width"], s["height"]


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()

    def tearDown(self):
        self.tmp.cleanup()

    def export(self, clips, *opts, check=True):
        tl = os.path.join(self.tmp.name, "timeline.json")
        out = os.path.join(self.tmp.name, "out.mp4")
        with open(tl, "w") as f:
            json.dump({"clips": [{"path": p, "in": a, "out": b} for p, a, b in clips]}, f)
        p = vericut("export", tl, out, "--encoder", ENCODER, *opts, check=check)
        if not check:
            return p
        return out, json.loads(p.stdout)

    def check_export(self, clips, *opts, expect_copy_only=False):
        """Export and verify against the spec. Returns the export report."""
        out, rep = self.export(clips, *opts)
        got = decoded_hashes(out)
        want = []
        for path, a, b in clips:
            want += decoded_hashes(path)[a:b]
        self.assertEqual(len(got), len(want), "frame count")
        self.assertEqual(rep["frames"], len(want))
        # which output positions are copies: segments are display-ordered runs
        kinds = []
        for seg in rep["segments"]:
            kinds += [seg["kind"]] * seg["frames"]
        self.assertEqual(len(kinds), len(want))
        for i, (k, g, w) in enumerate(zip(kinds, got, want)):
            if k == "copy":
                self.assertEqual(g, w, f"copied frame {i} differs from the source")
        if expect_copy_only:
            self.assertEqual(rep["reencoded"], 0)
            self.assertEqual(got, want)
        enc = [i for i, k in enumerate(kinds) if k == "encode"]
        if enc:
            w, h = size_of(out)
            gf = raw_frames(out, w, h)
            ref = []
            for path, a, b in clips:
                ref += raw_frames(path, w, h)[a:b]
            for i in enc:
                p = psnr(gf[i], ref[i])
                self.assertGreater(p, MIN_PSNR, f"re-encoded frame {i}: PSNR {p:.1f} dB")
        return rep


class ProbeTests(Base):
    """The demuxer agrees with ffprobe on every sample (differential test)."""

    def test_probe_matches_ffprobe(self):
        for name in sorted(os.listdir(SAMPLES)):
            if not name.endswith((".mp4", ".mov")):
                continue
            with self.subTest(name):
                ours = probe(sample(name))["frames"]
                ff = json.loads(run([FFPROBE, "-v", "error", "-select_streams", "v:0",
                                     "-show_entries", "packet=pts,dts,size,pos,flags",
                                     "-of", "json", sample(name)]).stdout)["packets"]
                self.assertEqual(len(ours), len(ff))
                for i, (o, f) in enumerate(zip(ours, ff)):
                    self.assertEqual(o["size"], int(f["size"]), f"size of sample {i}")
                    self.assertEqual(o["offset"], int(f["pos"]), f"offset of sample {i}")
                    self.assertEqual(o["keyframe"], "K" in f["flags"], f"keyframe flag of sample {i}")
                # sync = a keyframe the decoder can start from (IDR for H.264)
                if probe(sample(name))["codec"].startswith("avc"):
                    idr = idr_packets(sample(name))
                    self.assertEqual(len(idr), len(ours))
                    for i, (o, d) in enumerate(zip(ours, idr)):
                        self.assertEqual(o["sync"], o["keyframe"] and d, f"sync flag of sample {i}")
                else:
                    self.assertEqual([o["sync"] for o in ours], [o["keyframe"] for o in ours])
                # display order: our ranks sort the same way as ffprobe's pts
                by_pts = sorted(range(len(ff)), key=lambda i: (int(ff[i]["pts"]), i))
                ranks = [0] * len(ff)
                for r, i in enumerate(by_pts):
                    ranks[i] = r
                self.assertEqual([o["display"] for o in ours], ranks)


class CopyTests(Base):
    """Cuts that need no re-encoding are lossless and byte-identical."""

    def keyframes(self, path):
        return [f["display"] for f in probe(path)["frames"] if f["sync"]]

    def test_whole_clip_round_trip(self):
        for name in ["bbb_baseline.mp4", "gop24_bframes.mp4", "prores_intra.mov"]:
            with self.subTest(name):
                n = len(probe(sample(name))["frames"])
                out, rep = self.export([(sample(name), 0, n)])
                self.assertEqual(rep["reencoded"], 0)
                self.assertEqual(decoded_hashes(out), decoded_hashes(sample(name)))
                self.assertEqual(packet_hashes(out), packet_hashes(sample(name)))

    def test_keyframe_aligned_cut_is_byte_identical(self):
        for name in ["bbb_baseline.mp4", "gop30_nob.mp4", "gop24_bframes.mp4"]:
            with self.subTest(name):
                k = self.keyframes(sample(name))
                a, b = k[1], k[4]
                out, rep = self.export([(sample(name), a, b)], "--strict")
                self.assertEqual(rep["reencoded"], 0)
                self.assertEqual(decoded_hashes(out), decoded_hashes(sample(name))[a:b])
                src = packet_hashes(sample(name))
                self.assertEqual(sorted(packet_hashes(out)), sorted(src[a:b]))

    def test_intra_only_any_cut_copies(self):
        rep = self.check_export([(sample("prores_intra.mov"), 17, 93)], "--strict",
                                expect_copy_only=True)
        self.assertEqual(rep["copied"], 76)

    def test_multi_clip_copy(self):
        p = sample("prores_intra.mov")
        self.check_export([(p, 90, 110), (p, 5, 40), (p, 60, 61)], "--strict",
                          expect_copy_only=True)


class SmartCutTests(Base):
    """Mid-GOP cuts: boundary frames re-encoded, everything else copied exactly."""

    CASES = [
        ("gop30_nob.mp4", 45, 100),      # head re-encode, no B-frames
        ("gop24_bframes.mp4", 37, 150),  # head and tail re-encode, B-frames
        ("bbb_baseline.mp4", 100, 700),  # real footage
        ("bear_bframes.mp4", 10, 60),    # single long GOP: all re-encoded
    ]

    def test_smart_cut_stsd(self):
        for name, a, b in self.CASES:
            with self.subTest(name):
                self.check_export([(sample(name), a, b)], "--paramsets", "stsd")

    def test_smart_cut_inband(self):
        for name, a, b in self.CASES:
            with self.subTest(name):
                self.check_export([(sample(name), a, b)], "--paramsets", "inband")

    def test_reencodes_only_the_boundary(self):
        rep = self.check_export([(sample("bbb_baseline.mp4"), 100, 700)])
        k = [f["display"] for f in probe(sample("bbb_baseline.mp4"))["frames"] if f["sync"]]
        first_key = min(x for x in k if x >= 100)
        self.assertEqual(rep["reencoded"], first_key - 100)
        self.assertEqual(rep["copied"], 700 - first_key)

    def test_multi_clip_smart_cut(self):
        p = sample("bbb_baseline.mp4")
        self.check_export([(p, 500, 560), (p, 10, 200), (p, 1300, 1440)])


class OpenGopTests(Base):
    """Open GOP: stss also lists non-IDR I-frames, whose leading B-frames reference
    the previous GOP. Copy runs must not start at them."""

    def test_open_gop_keyframes_are_not_sync(self):
        frames = probe(sample(OPEN_GOP))["frames"]
        self.assertEqual([i for i, f in enumerate(frames) if f["keyframe"]], [0, 24, 46, 72, 95])
        self.assertEqual([i for i, f in enumerate(frames) if f["sync"]], [0])

    def test_open_gop_cuts(self):
        # [46, 90) starts at an I-frame, [40, 90) spans its leading B-frames 46, 47.
        for a, b in [(46, 90), (40, 90), (0, 90)]:
            with self.subTest((a, b)):
                self.check_export([(sample(OPEN_GOP), a, b)])

    def test_open_gop_whole_clip_round_trip(self):
        n = len(probe(sample(OPEN_GOP))["frames"])
        out, rep = self.export([(sample(OPEN_GOP), 0, n)], "--strict")
        self.assertEqual(decoded_hashes(out), decoded_hashes(sample(OPEN_GOP)))
        self.assertEqual(packet_hashes(out), packet_hashes(sample(OPEN_GOP)))


class RejectionTests(Base):
    """Bad requests fail loudly instead of writing a wrong file."""

    def test_strict_refuses_reencode(self):
        p = self.export([(sample("gop30_nob.mp4"), 45, 100)], "--strict", check=False)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("re-encoding", p.stderr)

    def test_bad_range(self):
        for a, b in [(10, 10), (50, 20), (0, 10_000)]:
            with self.subTest((a, b)):
                p = self.export([(sample("gop30_nob.mp4"), a, b)], check=False)
                self.assertNotEqual(p.returncode, 0)

    def test_mismatched_clips(self):
        p = self.export([(sample("gop30_nob.mp4"), 0, 30), (sample("bbb_baseline.mp4"), 0, 24)],
                        check=False)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("differs", p.stderr)


def mp4_boxes(b, s, e):
    while s + 8 <= e:
        sz, = struct.unpack(">I", b[s:s + 4])
        t, h = b[s + 4:s + 8].decode("latin1"), 8
        if sz == 1:
            sz, = struct.unpack(">Q", b[s + 8:s + 16])
            h = 16
        yield t, s + h, s + sz
        s += sz


def audio_edits(path):
    """The audio track's edit list as (samples, media time or -1), read independently of vericut."""
    with open(path, "rb") as f:
        b = f.read()
    moov = next(x for x in mp4_boxes(b, 0, len(b)) if x[0] == "moov")
    kids = list(mp4_boxes(b, *moov[1:]))
    mvhd = next(x for x in kids if x[0] == "mvhd")
    mts, = struct.unpack(">I", b[mvhd[1] + (20 if b[mvhd[1]] == 1 else 12):][:4])
    for t in kids:
        if t[0] != "trak":
            continue
        tk = list(mp4_boxes(b, *t[1:]))
        md = list(mp4_boxes(b, *next(x for x in tk if x[0] == "mdia")[1:]))
        hdlr = next(x for x in md if x[0] == "hdlr")
        if b[hdlr[1] + 8:hdlr[1] + 12] != b"soun":
            continue
        mdhd = next(x for x in md if x[0] == "mdhd")
        ats, = struct.unpack(">I", b[mdhd[1] + (20 if b[mdhd[1]] == 1 else 12):][:4])
        el = next(mp4_boxes(b, *next(x for x in tk if x[0] == "edts")[1:]))
        v, (n,), o, out = b[el[1]], struct.unpack(">I", b[el[1] + 4:el[1] + 8]), el[1] + 8, []
        for _ in range(n):
            if v == 1:
                d, m = struct.unpack(">Qq", b[o:o + 16]); o += 20
            else:
                d, m = struct.unpack(">Ii", b[o:o + 8]); o += 12
            assert d * ats % mts == 0, "audio edit not a whole number of samples"
            out.append((d * ats // mts, m))
        return out


def pcm(args):
    a = array.array("h")
    a.frombytes(run_bytes([FFMPEG, "-v", "error", *args, "-map", "0:a:0", "-ac", "1", "-f", "s16le", "-"]))
    return a


def present(media, edits):
    """What an ISO/IEC 14496-12 player plays: each edit's media samples, or silence."""
    out = array.array("h")
    for d, m in edits:
        out.extend(array.array("h", [0]) * d if m < 0 else media[m:m + d])
    return out


def frame_times(path):
    """Presentation time (s, exact) of each display frame, edit lists applied (ffprobe)."""
    tb = run([FFPROBE, "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=time_base",
              "-of", "csv=p=0", path]).stdout.strip()
    out = run([FFPROBE, "-v", "error", "-select_streams", "v:0", "-show_entries", "packet=pts",
               "-of", "csv=p=0", path]).stdout
    return sorted(int(l.split(",")[0]) * fractions.Fraction(tb) for l in out.split())


def nearest(x):
    """Round half up, as vericut's `sampleAt` does."""
    return math.floor(x + fractions.Fraction(1, 2))


def has_audio(path):
    return "audio" in run([FFPROBE, "-v", "error", "-show_entries", "stream=codec_type", "-of", "csv=p=0",
                           path]).stdout


class AudioTests(Base):
    """AAC audio is copied with a one-packet pre-roll per cut and trimmed by the
    edit list (`exportAudio_exact`, `exportAudio_synced`). Checked here against
    sources decoded by ffmpeg and timed by ffprobe, not against vericut's own numbers."""

    TIMELINES = [
        [(AV, 45, 100), (AV, 7, 61), (AV, 150, 180)],
        [(AV, 0, 40), ("gop30_nob.mp4", 10, 70), (AV, 100, 130)],   # middle clip has no audio
        [("bbb_baseline.mp4", 500, 560), ("bbb_baseline.mp4", 10, 200), ("bbb_baseline.mp4", 1300, 1440)],
    ]

    def expected(self, clips, rate):
        """Per clip: (source pcm, first source sample, output samples). The clip's
        audio starts at the sample nearest its first frame's time; its length runs
        to the sample nearest the next clip's start on the output clock."""
        out, t = [], 0
        for name, a, b in clips:
            path = sample(name)
            ft = frame_times(path)
            dur = ft[1] - ft[0]
            n = nearest((t + (b - a) * dur) * rate) - nearest(t * rate)
            src = pcm(["-i", path]) if has_audio(path) else None
            out.append((src, nearest(ft[a] * rate), n))
            t += (b - a) * dur
        return out

    def test_every_cut_plays_its_source_samples(self):
        for clips in self.TIMELINES:
            with self.subTest(clips):
                out, rep = self.export([(sample(p), a, b) for p, a, b in clips])
                rate = rep["audio"]["rate"]
                got = present(pcm(["-ignore_editlist", "1", "-i", out]), audio_edits(out))
                pos = 0
                for i, (src, start, n) in enumerate(self.expected(clips, rate)):
                    want = src[start:start + n] if src is not None else array.array("h")
                    want.extend(array.array("h", [0]) * (n - len(want)))  # past the source's end: silence
                    seg = got[pos:pos + n]
                    self.assertEqual(len(seg), n, f"clip {i}: audio length")
                    bad = [k for k in range(n) if seg[k] != want[k]]
                    self.assertEqual(bad, [], f"clip {i}: {len(bad)} samples differ from the source")
                    pos += n
                self.assertEqual(len(got), pos, "total audio length")
                self.assertEqual(rep["audio"]["samples"], pos)

    def test_audio_as_long_as_video(self):
        for clips in self.TIMELINES:
            with self.subTest(clips):
                out, rep = self.export([(sample(p), a, b) for p, a, b in clips])
                ft = frame_times(out)
                video = len(ft) * (ft[1] - ft[0])
                audio = fractions.Fraction(sum(d for d, _ in audio_edits(out)), rep["audio"]["rate"])
                self.assertLessEqual(2 * abs(audio - video), fractions.Fraction(1, rep["audio"]["rate"]))

    @unittest.skipUnless(sys.platform == "darwin" and shutil.which("swiftc"), "AVFoundation (macOS)")
    def test_avfoundation_plays_the_cuts(self):
        """QuickTime/AVFoundation, the app's player, honours the multi-entry edit list."""
        tool = os.path.join(self.tmp.name, "avpcm")
        run(["swiftc", "-O", os.path.join(ROOT, "tests/avpcm.swift"), "-o", tool])

        def av(path):
            a = array.array("h")
            a.frombytes(run_bytes([tool, path]))
            return a

        clips = self.TIMELINES[0]
        out, rep = self.export([(sample(p), a, b) for p, a, b in clips])
        got, src, pos = av(out), av(sample(AV)), 0
        for i, (_, start, n) in enumerate(self.expected(clips, rep["audio"]["rate"])):
            m = min(n, len(got) - pos)  # AVFoundation leaves out trailing empty edits
            bad = [k for k in range(m) if abs(got[pos + k] - src[start + k]) > 1]
            self.assertEqual(bad, [], f"clip {i}: AVFoundation output differs from the source")
            pos += n

    def test_no_audio_flag(self):
        out, rep = self.export([(sample(AV), 45, 100)], "--no-audio")
        self.assertFalse(has_audio(out))
        self.assertIsNone(rep["audio"])

    def test_video_unchanged_by_audio(self):
        self.check_export([(sample(AV), 45, 100), (sample(AV), 7, 61)])


class ProofAuditTests(unittest.TestCase):
    """The main theorems use no `sorry` and no axioms beyond Lean's standard three."""

    MAIN = ["picture_extract", "decode_extract", "decode_concatStreams", "export_correct",
            "export_exact", "copySet_copyable", "copyable_maximal", "table_eq_copyable",
            "plan_valid", "plan_covers", "plan_copy_copyable",
            "exportTimeline_correct", "MP4.toStream_wellFormed",
            "exportAudio_exact", "exportAudio_synced", "exportAudio_aligned"]
    ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

    def test_axioms(self):
        core = os.path.join(ROOT, "core")
        src = "import VeriCut\n" + "".join(f"#print axioms VeriCut.{t}\n" for t in self.MAIN)
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
            f.write(src)
        try:
            p = subprocess.run(["lake", "env", "lean", f.name], cwd=core, capture_output=True, text=True)
        finally:
            os.unlink(f.name)
        self.assertEqual(p.returncode, 0, p.stderr + p.stdout)
        lines = [l for l in p.stdout.splitlines() if "depends on axioms" in l or "does not depend" in l]
        self.assertEqual(len(lines), len(self.MAIN), p.stdout)
        for l in lines:
            if "depends on axioms" in l:
                axs = set(l.split("[", 1)[1].rstrip("]").replace(" ", "").split(","))
                self.assertTrue(axs <= self.ALLOWED, l)


if __name__ == "__main__":
    unittest.main(verbosity=2)
