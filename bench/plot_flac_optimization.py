# /// script
# dependencies = ["matplotlib"]
# ///
"""Plot bench/flac-optimization.csv: vericut relative to libFLAC, per commit."""
import csv, pathlib, sys
import matplotlib.pyplot as plt

here = pathlib.Path(__file__).parent
rows = list(csv.DictReader(open(here / "flac-optimization.csv")))
latest = {(r["commit"], r["clip"], r["tool"], r["level"]): r for r in rows}  # reruns: keep last
commits = list(dict.fromkeys(r["commit"] for r in rows if r["tool"] == "vericut"))
labels = {r["commit"]: r["description"].split(":")[0].split(" (")[0][:18] for r in rows}
ref = lambda clip, lvl, k: float(latest[("ref", clip, "flac", lvl)][k])

def series(clip, lvl, k, rel=True):
    xs, ys = [], []
    for i, c in enumerate(commits):
        r = latest.get((c, clip, "vericut", lvl))
        if r:
            xs.append(i)
            ys.append(float(r[k]) / ref(clip, lvl, k) if rel else float(r[k]))
    return xs, ys

fig, ax = plt.subplots(2, 2, figsize=(14, 9))
clips = ["piano", "forest", "podcast"]
panels = [
    (ax[0, 0], "encode_s", "5", True, "Encode time vs libFLAC -5 (×, log)"),
    (ax[0, 1], "decode_s", "5", True, "Decode time vs libFLAC (×, log)"),
    (ax[1, 0], "output_bytes", "8", True, "Output size vs libFLAC -8 (×)"),
    (ax[1, 1], "peak_rss_mb", "5", False, "Peak RSS, -5 (MB, log)"),
]
for a, k, lvl, rel, title in panels:
    for clip in clips:
        xs, ys = series(clip, lvl, k, rel)
        a.plot(xs, ys, "o-", label=clip)
    a.set_title(title)
    if k != "output_bytes":
        a.set_yscale("log")
    else:
        a.axhline(1, color="gray", lw=0.8, ls="--")
    a.set_xticks(range(len(commits)))
    a.set_xticklabels([f"{c}\n{labels[c]}" for c in commits], rotation=35, ha="right", fontsize=7)
    a.grid(alpha=0.3)
    a.legend(fontsize=8)
fig.suptitle("vericut (verified Lean FLAC) optimization progress")
fig.tight_layout()
out = here / "flac-optimization.png"
fig.savefig(out, dpi=150)
print(out)
