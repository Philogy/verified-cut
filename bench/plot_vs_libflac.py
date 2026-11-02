# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib"]
# ///
"""Bar chart of vericut vs libFLAC at -5 (commit 95565b4, median wall time). Writes bench/vs-libflac.png."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).parent
VC, LF = "#c0392b", "#2c3e50"
plt.rcParams.update({"font.size": 15, "axes.titlesize": 17,
                     "axes.spines.top": False, "axes.spines.right": False})

# (title, clips, vericut, libFLAC, value format)
panels = [
    ("encode (s)", ["piano", "forest"], [1.160, 0.509], [0.067, 0.034], "{:.2f}"),
    ("size (% of WAV)", ["piano", "forest"], [37.26, 18.64], [37.33, 18.78], "{:.1f}"),
    ("decode (s)", ["piano"], [0.329], [0.042], "{:.2f}"),
]

fig, axes = plt.subplots(1, 3, figsize=(12, 4.6), gridspec_kw={"width_ratios": [2, 2, 1.2]})
w = 0.38
for ax, (title, clips, vc, lf, fmt) in zip(axes, panels):
    xs = range(len(clips))
    for dx, vals, color, label in [(-w / 2, vc, VC, "vericut"), (w / 2, lf, LF, "libFLAC")]:
        bars = ax.bar([x + dx for x in xs], vals, w, color=color, label=label)
        ax.bar_label(bars, [fmt.format(v) for v in vals], padding=3, fontsize=12)
    ax.set_xticks(list(xs), clips)
    ax.set_title(title)
    ax.set_yticks([])
    ax.spines["left"].set_visible(False)
    ax.margins(y=0.15)
axes[0].legend(frameon=False, loc="upper right")
fig.tight_layout()
fig.savefig(HERE / "vs-libflac.png", dpi=150, transparent=True)
print("wrote", HERE / "vs-libflac.png")
