# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib", "pillow"]
# ///
"""Pareto frontier animation and static plots from bench/flac-optimization.csv.

Writes bench/pareto.gif, bench/pareto.mp4 (if ffmpeg exists), bench/pareto-final.png
and bench/flac-progress.png.
"""
import csv, shutil, subprocess
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation, PillowWriter

HERE = Path(__file__).parent
CLIPS = ["piano", "forest"]
plt.rcParams.update({"font.size": 15, "axes.titlesize": 18, "axes.labelsize": 16,
                     "axes.spines.top": False, "axes.spines.right": False})
VC, LF = "#c0392b", "#2c3e50"

rows = list(csv.DictReader(open(HERE / "flac-optimization.csv")))
# best (min) encode time per commit/clip/tool/level; ratio and other columns from that row
# 85b3612 only bumps the toolchain to 4.35 (7-15% slower encode); not an optimization step
SKIP = {"85b3612"}
best, order, desc, first_ts = {}, [], {}, {}
for r in rows:
    c = r["commit"][:7]
    if c in SKIP:
        continue
    if r["tool"] == "vericut" and c not in first_ts:
        first_ts[c] = r["timestamp"]
        d = r["description"].split(":")[0].split(" (")[0]
        desc[c] = d[:60]
    k = (c, r["clip"], r["tool"], int(r["level"]))
    if k not in best or float(r["encode_s"]) < float(best[k]["encode_s"]):
        best[k] = r
order = sorted(first_ts, key=first_ts.get)

def points(commit, clip, tool):
    return sorted((float(r["encode_s"]), float(r["ratio"]), lv)
                  for (c, cl, t, lv), r in best.items() if (c, cl, t) == (commit, clip, tool))

def frontier(pts):
    """Points not dominated in (time, ratio), both lower-better, sorted by time."""
    out, br = [], float("inf")
    for t, r, _ in sorted(pts):
        if r < br:
            out.append((t, r)); br = r
    return out

def step(ax, fr, **kw):
    xs, ys = [], []
    for i, (t, r) in enumerate(fr):
        if i: xs.append(t); ys.append(fr[i - 1][1])
        xs.append(t); ys.append(r)
    return ax.plot(xs, ys, drawstyle="default", **kw)

allpts = [p for c in order + ["ref"] for cl in CLIPS for tool in ("vericut", "flac")
          for p in points(c, cl, tool)]
xlim = (min(p[0] for p in allpts) / 1.5, max(p[0] for p in allpts) * 1.5)

def draw(axes, upto):
    for ax, clip in zip(axes, CLIPS):
        ax.clear()
        ref = points("ref", clip, "flac")
        ys = [p[1] for c in order for p in points(c, clip, "vericut")] + [p[1] for p in ref]
        ax.set_xscale("log"); ax.set_xlim(*xlim)
        ax.set_ylim(min(ys) - 0.01, max(ys) + 0.015)
        step(ax, frontier(ref), color=LF, lw=2.5, label="libFLAC -0..-8")
        ax.scatter([p[0] for p in ref], [p[1] for p in ref], color=LF, s=40, zorder=3)
        for i, c in enumerate(order[:upto]):
            fr = frontier(points(c, clip, "vericut"))
            a = 0.12 + 0.25 * i / max(1, upto)
            step(ax, fr, color=VC, lw=1.5, alpha=a)
        c = order[upto]
        pts = points(c, clip, "vericut")
        step(ax, frontier(pts), color=VC, lw=3, label="vericut (verified)")
        ax.scatter([p[0] for p in pts], [p[1] for p in pts], color=VC, s=70, zorder=4)
        for t, r, lv in pts:
            ax.annotate(f"-{lv}", (t, r), textcoords="offset points", xytext=(6, 4),
                        fontsize=11, color=VC)
        ax.set_title(f"{clip}")
        ax.set_xlabel("encode time (s, log)")
        ax.grid(alpha=0.3, which="both")
    axes[0].set_ylabel("compressed size / WAV size")
    axes[0].legend(loc="upper right", fontsize=13, frameon=False)

def animate():
    fig, axes = plt.subplots(1, 2, figsize=(15, 6.5))
    hold = 6
    frames = list(range(len(order))) + [len(order) - 1] * hold
    def upd(i):
        draw(axes, frames[i])
        c = order[frames[i]]
        fig.suptitle(f"Size vs. speed, step {frames[i] + 1}/{len(order)}:  {c}  {desc[c]}",
                     fontsize=17, x=0.02, ha="left")
        fig.tight_layout(rect=(0, 0, 1, 0.94))
    anim = FuncAnimation(fig, upd, frames=len(frames))
    # dpi 160: 2400 px wide, so the slide (and README) only ever scales it down
    anim.save(HERE / "pareto.gif", writer=PillowWriter(fps=1), dpi=160)
    if shutil.which("ffmpeg"):
        tmp = HERE / "_frames"; tmp.mkdir(exist_ok=True)
        for i in range(len(order)):
            upd(i); fig.savefig(tmp / f"{i:03d}.png", dpi=100)
        subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-framerate", "1",
                        "-i", str(tmp / "%03d.png"), "-vf",
                        "tpad=stop_mode=clone:stop_duration=4,fps=24,scale=trunc(iw/2)*2:trunc(ih/2)*2",
                        "-pix_fmt", "yuv420p", str(HERE / "pareto.mp4")], check=True)
        shutil.rmtree(tmp)
    # final frame as a static comparison
    draw(axes, len(order) - 1)
    fig.suptitle(f"Final: vericut {order[-1]} vs. libFLAC (first frontier faded)",
                 fontsize=17, x=0.02, ha="left")
    # only show the first and last vericut frontier on the static plot
    for ax, clip in zip(axes, CLIPS):
        for ln in ax.lines[1:-1]:
            ln.remove()
        step(ax, frontier(points(order[0], clip, "vericut")), color=VC, lw=1.5, alpha=0.3,
             ls="--", label=f"vericut start ({order[0]})")
    axes[0].legend(loc="upper right", fontsize=13, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    fig.savefig(HERE / "pareto-final.png", dpi=110)
    plt.close(fig)

def progress():
    fig, axes = plt.subplots(1, 3, figsize=(18, 6))
    x = range(len(order))
    def series(clip, col, lv=5):
        return [float(best[(c, clip, "vericut", lv)][col]) if (c, clip, "vericut", lv) in best
                else float("nan") for c in order]
    def ref(clip, col, lv=5):
        k = ("ref", clip, "flac", lv)
        return float(best[k][col]) if k in best else None
    for ax, col, title in ((axes[0], "encode_s", "encode time, -5 (s)"),
                           (axes[1], "decode_s", "decode time (s)")):
        for clip, mk in (("piano", "o"), ("podcast", "s")):
            ys = series(clip, col); xs = [i for i in x if ys[i] == ys[i]]
            ax.plot(xs, [ys[i] for i in xs], marker=mk, color=VC if clip == "piano" else "#e67e22",
                    lw=2.5, ms=8, label=f"vericut {clip}")
            rv = ref(clip, col)
            if rv: ax.axhline(rv, color=VC if clip == "piano" else "#e67e22", ls=":", lw=2,
                              label=f"libFLAC {clip}")
        ax.set_yscale("log"); ax.set_title(title)
    pod = series("podcast", "peak_rss_mb")
    px = [i for i in x if pod[i] == pod[i]]
    axes[2].plot(px, [pod[i] / 1024 for i in px], marker="s", color="#e67e22", lw=2.5, ms=8,
                 label="vericut podcast (61 min)")
    axes[2].set_title("peak RSS, podcast encode (GB)"); axes[2].set_ylim(bottom=0)
    for ax in axes:
        ax.set_xticks(list(x)); ax.set_xticklabels(order, rotation=60, fontsize=11)
        ax.grid(alpha=0.3, which="both"); ax.legend(fontsize=11, frameon=False)
    fig.suptitle("Optimization history (each step keeps the round-trip proofs)",
                 fontsize=18, x=0.02, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    fig.savefig(HERE / "flac-progress.png", dpi=110)
    plt.close(fig)

animate()
progress()
print("ok", order)
