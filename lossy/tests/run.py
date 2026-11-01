#!/usr/bin/env python3
"""Tests for the lossy codec, and a size/error benchmark.

  python3 tests/run.py            synthetic signals: round trip, error bounds,
                                  monotonicity, reference decoders agree
  python3 tests/run.py --bench    real clips under ../samples/audio: size and
                                  error against q, vs flac, lame, aac
"""
import array, json, math, os, random, subprocess, sys, tempfile, wave

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.environ.get("LOSSY_BIN", os.path.join(HERE, "..", ".lake", "build", "bin", "lossy"))
AUDIO = os.environ.get("LOSSY_AUDIO", os.path.join(HERE, "..", "..", "samples", "audio"))
TMP = tempfile.mkdtemp(prefix="lossy-")
LIMIT = 600  # seconds for any one external command


def run(*args, ok=(0,)):
    p = subprocess.run(list(args), capture_output=True, timeout=LIMIT)
    if p.returncode not in ok:
        raise RuntimeError(f"{args}: exit {p.returncode}: {p.stderr.decode()[-500:]}")
    return p.stdout


def write_wav(path, rate, bits, chans):
    """chans: list of equal-length lists of ints."""
    n, ch, width = len(chans[0]), len(chans), bits // 8
    frames = bytearray()
    for i in range(n):
        for c in chans:
            frames += (c[i] % (1 << bits)).to_bytes(width, "little")
    with wave.open(path, "wb") as w:
        w.setnchannels(ch); w.setsampwidth(width); w.setframerate(rate)
        w.writeframes(bytes(frames))


def pcm(path):
    """Interleaved signed samples as decoded by ffmpeg, 32-bit."""
    return array.array("i", run("ffmpeg", "-v", "error", "-i", path, "-f", "s32le", "-"))


def stats(q, wav):
    return json.loads(run(BIN, "stats", str(q), wav, ok=(0, 2)))


def synthetic():
    r = random.Random(1)
    n = 3 * 4096 + 17  # not a whole number of blocks
    sine = [round(12000 * math.sin(2 * math.pi * 440 * i / 44100)) for i in range(n)]
    quiet = [round(40 * math.sin(2 * math.pi * 220 * i / 44100)) for i in range(n)]
    noise = [r.randint(-32768, 32767) for _ in range(n)]
    square = [32767 if (i // 50) % 2 else -32768 for i in range(n)]
    sweep24 = [round(8000000 * math.sin(2 * math.pi * (20 + i / 20) * i / 48000)) for i in range(n)]
    return {
        "silence": (44100, 16, [[0] * n, [0] * n]),
        "sine": (44100, 16, [sine, [-v for v in sine]]),
        "quiet_then_loud": (44100, 16, [quiet[:4096] + sine[4096:], quiet[:4096] + sine[4096:]]),
        "noise": (44100, 16, [noise, noise[::-1]]),
        "full_scale_square": (44100, 16, [square, square]),
        "mono24_sweep": (48000, 24, [sweep24]),
        "one_sample": (8000, 16, [[-32768]]),
        "eight_channels": (22050, 16, [[(i * (c + 1) * 97) % 65536 - 32768 for i in range(5000)] for c in range(8)]),
    }


def test():
    qs = [0, 1, 2, 4, 8, 12, 16]
    fails = 0
    for name, (rate, bits, chans) in synthetic().items():
        wav = os.path.join(TMP, name + ".wav")
        write_wav(wav, rate, bits, chans)
        rows = [stats(q, wav) for q in qs]
        problems = []
        for q, s in zip(qs, rows):
            if not s["roundTrip"]: problems.append(f"q={q} decode != quantize")
            if s["maxErr"] >= 2 ** q: problems.append(f"q={q} maxErr {s['maxErr']} >= 2^{q}")
        if rows[0]["maxErr"] or rows[0]["sqErr"]: problems.append("q=0 not lossless")
        for a, b in zip(rows, rows[1:]):
            if b["maxErr"] < a["maxErr"] or b["sqErr"] < a["sqErr"]:
                problems.append(f"error fell from q={a['q']} to q={b['q']}")
        for q in (0, 8):
            flac = os.path.join(TMP, f"{name}.{q}.flac")
            ours = os.path.join(TMP, f"{name}.{q}.wav")
            run(BIN, "encode", str(q), wav, flac)
            run(BIN, "decode", flac, ours)
            run("flac", "-t", "-s", flac)
            if pcm(flac) != pcm(ours): problems.append(f"q={q} ffmpeg and our decoder differ")
            if q == 0 and pcm(flac) != pcm(wav): problems.append("q=0 ffmpeg decode != input")
        sizes = " ".join(str(s["bytes"]) for s in rows)
        print(f"{'FAIL' if problems else 'ok  '} {name:18} bytes q={qs}: {sizes}")
        for p in problems: print("     ", p)
        fails += bool(problems)
    print(f"{len(synthetic()) - fails}/{len(synthetic())} passed")
    return fails == 0


def snr(ref, out):
    n = min(len(ref), len(out))
    sig = sum(v * v for v in ref[:n])
    err = sum((a - b) ** 2 for a, b in zip(ref[:n], out[:n]))
    return math.inf if err == 0 else 10 * math.log10(sig / err)


def bench(clips):
    lines = ["| clip | codec | setting | bytes | ratio vs WAV | SNR dB | maxErr | encode ms |",
             "|---|---|---|---|---|---|---|---|"]
    for path in clips:
        name = os.path.basename(path)
        wav_bytes = os.path.getsize(path)
        ref = pcm(path)
        sig = sum(v * v for v in ref) or 1
        scale = 1 << 16  # ffmpeg's s32le puts 16-bit samples in the top bits
        for q in [0, 2, 4, 6, 8, 10, 12]:
            s = stats(q, path)
            d = math.inf if s["sqErr"] == 0 else 10 * math.log10(sig / (s["sqErr"] * scale * scale))
            lines.append(f"| {name} | lossy | q={q} | {s['bytes']} | {s['bytes'] / wav_bytes:.3f} | "
                         f"{d:.1f} | {s['maxErr']} | {s['encodeMs']} |")
            print(lines[-1], flush=True)
        # "same tools": what our encoder uses (fixed predictors, one Rice
        # partition, independent channels, 4096-sample blocks)
        for lvl, args in (("same tools", ["-0", "-l", "0", "--no-mid-side", "-b", "4096", "-r", "0"]),
                          ("-5", ["-5"]), ("-8", ["-8"])):
            out = os.path.join(TMP, "ref.flac")
            run("flac", "-f", "-s", *args, "-o", out, path)
            lines.append(f"| {name} | flac | {lvl} | {os.path.getsize(out)} | "
                         f"{os.path.getsize(out) / wav_bytes:.3f} | inf | 0 | |")
        for codec, ext, rates in (("libmp3lame", "mp3", ["128k", "320k"]), ("aac", "m4a", ["128k", "256k"])):
            for br in rates:
                out = os.path.join(TMP, f"ref.{ext}")
                run("ffmpeg", "-v", "error", "-y", "-i", path, "-c:a", codec, "-b:a", br, out)
                lines.append(f"| {name} | {codec} | {br} | {os.path.getsize(out)} | "
                             f"{os.path.getsize(out) / wav_bytes:.3f} | {snr(ref, pcm(out)):.1f} | | |")
        print("\n".join(lines[-6:]), flush=True)
    return "\n".join(lines)


if __name__ == "__main__":
    if "--bench" in sys.argv:
        clips = [a for a in sys.argv[1:] if a != "--bench"] or sorted(
            os.path.join(AUDIO, f) for f in os.listdir(AUDIO)
            if f.endswith(".wav") and not f.endswith(".orig.wav") and "dwarkesh" not in f)
        table = bench(clips)
        with open(os.path.join(HERE, "..", "RESULTS.md"), "w") as f:
            f.write("# lossy: size and error\n\n" + table + "\n")
    else:
        sys.exit(0 if test() else 1)
