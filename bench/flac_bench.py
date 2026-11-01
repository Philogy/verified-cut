#!/usr/bin/env python3
"""Append FLAC encode/decode benchmark rows to bench/flac-optimization.csv.

    bench/flac_bench.py DESCRIPTION [--tools vericut,flac,ffmpeg] [--clips piano,forest]
                        [--levels 0,5,8] [--runs 5] [--bin PATH]

Each (clip, tool, level) is run `--runs` times for encode and for decode; wall
times are the median, peak RSS the max over the runs (from wait4). Decode
times decode the tool's own output. Every vericut output is checked bit-exact
with `flac -d` against the source WAV's samples, and with `flac -t`.
"""
import argparse, csv, datetime, hashlib, os, statistics, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CSV = os.path.join(ROOT, "bench/flac-optimization.csv")
AUDIO = os.path.join(ROOT, "samples/audio")
CLIPS = {
    "vine": "meme_vine_boom.wav",
    "piano": "music_relaxing_piano.wav",
    "forest": "ambience_forest.wav",
    "podcast": "dwarkesh_robert_caro.wav",
}
COLS = ["commit", "timestamp", "description", "clip", "tool", "level", "encode_s", "decode_s",
        "peak_rss_mb", "output_bytes", "ratio"]
TMP = tempfile.mkdtemp(prefix="flacbench-")


def timed(cmd, timeout):
    """Wall seconds and peak RSS (MB) of one run."""
    t0 = time.perf_counter()
    p = subprocess.Popen(["nice", "-n", "5", *cmd], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    try:
        _, status, ru = os.wait4(p.pid, 0)
    except BaseException:
        p.kill()
        raise
    dt = time.perf_counter() - t0
    p.returncode = os.waitstatus_to_exitcode(status)
    if p.returncode != 0:
        raise RuntimeError(f"{cmd} failed: {p.stderr.read().decode()[-500:]}")
    if dt > timeout:
        raise RuntimeError(f"{cmd} took {dt:.0f}s > {timeout}s")
    return dt, ru.ru_maxrss / 2**20  # macOS: bytes


def cmds(tool, level, src, flac_out, wav_out, binary):
    if tool == "vericut":
        return ([binary, "encode", src, flac_out, "--level", str(level)],
                [binary, "decode", flac_out, wav_out])
    if tool == "flac":
        return (["flac", "-s", "-f", f"-{level}", "-o", flac_out, src],
                ["flac", "-s", "-f", "-d", "-o", wav_out, flac_out])
    if tool == "ffmpeg":
        return (["ffmpeg", "-v", "error", "-y", "-i", src, "-c:a", "flac", "-compression_level", str(level), flac_out],
                ["ffmpeg", "-v", "error", "-y", "-i", flac_out, "-f", "wav", wav_out])
    raise ValueError(tool)


def pcm_md5(path):
    """MD5 of the raw samples, via flac (for .flac) or ffmpeg's s16/s24 view (wav)."""
    out = subprocess.run(["ffmpeg", "-v", "error", "-i", path, "-f", "s16le", "-"], capture_output=True, check=True)
    return hashlib.md5(out.stdout).hexdigest()


def check_exact(src, flac_out):
    subprocess.run(["flac", "-s", "-t", flac_out], check=True, capture_output=True)
    dec = os.path.join(TMP, "check.wav")
    subprocess.run(["flac", "-s", "-f", "-d", "-o", dec, flac_out], check=True, capture_output=True)
    if pcm_md5(dec) != pcm_md5(src):
        raise RuntimeError(f"{flac_out}: flac -d differs from {src}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("description")
    ap.add_argument("--tools", default="vericut")
    ap.add_argument("--clips", default="piano,forest")
    ap.add_argument("--levels", default="0,5,8")
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--timeout", type=float, default=900)
    ap.add_argument("--bin", default=os.path.join(ROOT, "core/.lake/build/bin/vericut"))
    ap.add_argument("--commit", default=None)
    a = ap.parse_args()
    commit = a.commit or subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"],
                                        capture_output=True, text=True, check=True).stdout.strip()
    new = not os.path.exists(CSV)
    with open(CSV, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(COLS)
        for clip in a.clips.split(","):
            src = os.path.join(AUDIO, CLIPS[clip])
            wav_bytes = os.path.getsize(src)
            for tool in a.tools.split(","):
                for level in [int(l) for l in a.levels.split(",")]:
                    fo = os.path.join(TMP, f"{clip}-{tool}-{level}.flac")
                    wo = os.path.join(TMP, f"{clip}-{tool}-{level}.wav")
                    enc, dec = cmds(tool, level, src, fo, wo, a.bin)
                    runs = a.runs if clip != "podcast" else min(a.runs, 1)
                    e = [timed(enc, a.timeout) for _ in range(runs)]
                    if tool == "vericut":
                        check_exact(src, fo)
                    d = [timed(dec, a.timeout) for _ in range(runs)]
                    size = os.path.getsize(fo)
                    row = [commit, datetime.datetime.now().isoformat(timespec="seconds"), a.description, clip, tool,
                           level, f"{statistics.median(x[0] for x in e):.3f}",
                           f"{statistics.median(x[0] for x in d):.3f}",
                           f"{max(x[1] for x in e + d):.0f}", size, f"{size / wav_bytes:.4f}"]
                    w.writerow(row)
                    f.flush()
                    print(",".join(map(str, row)), flush=True)
                    for p in (fo, wo):
                        if os.path.exists(p):
                            os.remove(p)


if __name__ == "__main__":
    main()
