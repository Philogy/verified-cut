# Can plain ffmpeg do a frame-exact smart cut?

## Verdict

**One ffmpeg call cannot do it.** No option, filter, bitstream filter, muxer or
demuxer in ffmpeg 9.0.2 (checked against the 7.x–9.0 docs and changelogs) does a
frame-exact cut that also stream-copies the untouched GOPs. Every single call
does one of these instead:

- re-encodes everything (`-ss`/`trim`/`select` + an encoder): exact, but no
  frame is copied;
- copies but snaps to keyframes (output `-ss`, `-seek2any`, segment muxer,
  concat `inpoint`): wrong frames;
- copies and hides the lead-in with an MP4 edit list (input `-ss … -c copy`):
  only "exact" in players that honour edit lists, wrong in players that ignore
  them, and wrong at the tail on B-frame streams. MP4 output keeps only one edit
  list entry, so it can't express several ranges either.

Filters and stream copy can't be combined on a stream ("Filtering and
streamcopy cannot be used together", trac #8004), so a re-encode at the edges and
a copy in the middle can't happen in one output stream. Smart rendering has been
proposed on ffmpeg-devel twice (2020, 2025). Nothing was merged; the maintainer's
reply in 2025 was "clean patch welcome".

**Several ffmpeg calls can do it**, with no edit lists and no keyframe snapping:

1. re-encode each head (and B-frame tail) by frame number;
2. stream-copy each whole closed GOP by *packet index* using the `noise`
   bitstream filter's `drop` expression;
3. join the pieces with the concat demuxer (`-c copy`). Its default
   `auto_convert=1` puts SPS/PPS in-band, so the copied packets keep their own
   parameter sets.

Measured on both samples, this recipe gives output identical to vericut's: the
same frame count, every copied frame bit-identical, and re-encoded frames at
≥43 dB, decoded with both ffmpeg and AVFoundation. **ffmpeg can't plan the
pieces itself, though.** Which frames to re-encode and which packets can be
copied (keyframe positions, B-frame reorder at the tail, closed or open GOP) had
to be worked out outside ffmpeg, from an `ffprobe` packet dump. That planning is
exactly vericut's proven `plan`. ffmpeg is only the executor, which is how
vericut already uses it.

**A side finding that matters for the closed-GOP assumption:** in an ffmpeg/x264
open-GOP MP4, non-IDR I-frames are listed in `stss`. vericut then copies the
open GOP's leading B-frames and gets wrong output (details in §4).

## 1. Sources

- The concat demuxer (`doc/demuxers.texi`) says `inpoint`/`outpoint` work "best
  with intra frame codecs". For other codecs "you will usually get extra
  packets before the actual In point and the decoded content will most likely
  contain frames before In point too", and the same happens after the Out point.
  `auto_convert` (default 1) applies `h264_mp4toannexb` so the streams can be
  concatenated. https://raw.githubusercontent.com/FFmpeg/FFmpeg/master/doc/demuxers.texi
- `noise` bsf (`doc/bitstream_filters.texi`): `drop` is an expression evaluated
  per packet, with the variables `n` (packet index), `pts`, `dts`, `key`, …. The
  doc's own example drops packets by time and keyframe flag.
  https://raw.githubusercontent.com/FFmpeg/FFmpeg/master/doc/bitstream_filters.texi
- Seeking wiki: `-ss` with `-c copy` starts at the keyframe at or before the
  requested time. https://trac.ffmpeg.org/wiki/Seeking (I only read search
  snippets; Anubis blocked the page.)
- Filters with copy: https://trac.ffmpeg.org/ticket/8004. I reproduced the error
  locally (§2, row 11).
- ffmpeg-devel, "An idea to Mix re-encoding with copy to get a fast and precise
  cut" (2020-07, no patch):
  https://ffmpeg.org/pipermail/ffmpeg-devel/2020-July/266700.html
- ffmpeg-devel, "Cut a video (-ss) with timings non-aligned on keyframes, with
  minimal re-encoding" (2025-07). Niedermayer replied "clean patch welcome" and
  tied it to edit-list rendering. No patch followed.
  https://ffmpeg.org/pipermail/ffmpeg-devel/2025-July/346918.html
- Changelogs for n8.0 and n9.0 (8.0, 8.1, 9.0): no cutting, smart-render or
  edit-list feature. https://raw.githubusercontent.com/FFmpeg/FFmpeg/n9.0/Changelog
- Tools that do smart cuts, all outside the ffmpeg CLI. Each plans the cut itself
  and uses libav* or ffmpeg only to execute it:
  - LosslessCut "smart cut", experimental since v3.44, re-encodes the first
    partial GOP and concatenates. It is known to be flaky: H.264 only reliably,
    and it can produce duplicate segments.
    https://github.com/mifi/lossless-cut/issues/126
  - skeskinen/smartcut (PyAV) re-encodes around the cut points.
    https://github.com/skeskinen/smartcut
  - Avidemux had "smart copy" in 2.5.x and dropped it in 2.6 because of AVC
    reordering. https://avidemux.org/smif/index.php?msg=57033

## 2. Single-call experiments

Setup:
- ffmpeg 9.0.2.
- `bbb_baseline.mp4`: 24 fps, Constrained Baseline, no B-frames, keyframe every
  64 frames.
- `gop24_bframes.mp4`: 30 fps, High profile, 2 B-frames, closed GOP of 24.
- Cut [100,200) on bbb and [10,50) on gop24 (40 frames). Neither start is on a
  keyframe.
- "ff" columns: ffprobe frame count with the edit list honoured / ignored, then
  the packet count.
- "exact": per-frame PSNR against the source frames
  `select=between(n,a,b-1)`, decoded by ffmpeg. "avf" is the same comparison
  decoded by AVFoundation (`AVAssetReader`, which honours edit lists), Y plane
  only.

| # | command (`-map 0:v -c copy` unless noted) | bbb (want 100) ff | bbb exact / avf | gop24 (want 40) ff | gop24 exact / avf |
|---|---|---|---|---|---|
| 1 | `-ss A -to B -i src` (default) | 100 / 136 / 136 pkts | 100/100 / 100/100 | 43 / 53 / 53 | 40/43 / 40/43 |
| 2 | 1 + `-use_editlist 0` | 136 / 136 | 1/136 / 1/136 | 53 / 53 | 1/53 / 1/51 |
| 3 | 1 + `-avoid_negative_ts make_zero` | 136 / 136 | 1/136 / 1/136 | 53 / 53 | 1/53 / 1/54 |
| 4 | 1 + `-copyts` | 136 / 136 | 1/136 / 1/137 | 52 / 52 | 1/52 / 1/52 |
| 5 | 1 + `-noaccurate_seek` | same as 1 | same as 1 | same as 1 | same as 1 |
| 6 | output `-i src -ss A -to B` | 72 | 1/100 (starts at next keyframe) | 28 | 0/40 |
| 7 | 6 + `-copyinkf` | 72 decodable of 100 pkts | AVFoundation fails | 28 of 40 | AVFoundation fails |
| 8 | `-seek2any 1 -ss A -i src` | 72 | 1/100 | 29 | 0/40 |
| 9 | `-ss A -to B -i src -c:v libx264` (re-encode) | 100 | 0/100, min 44 dB | 40 | 0/40, min 46 dB |
| 10 | concat demuxer, 2 ranges, `inpoint`/`outpoint` | 268 (want 200) | 0/268 | 109 (want 90) | 1/109 |
| 11 | `-vf trim=… -c:v copy` | error: "Filtering and streamcopy cannot be used together" | | | |
| 12 | segment muxer `-segment_frames 100,200` | splits at 128, 256 (next keyframes) | | | |
| 13 | two row-1 pieces → concat demuxer | 244 (want 200) | 101/244 | | |

How to read the table:
- Row 1 is ffmpeg's "accurate" stream-copy cut. It copies from the previous
  keyframe and writes an `elst` whose media time skips the lead-in: 36 hidden
  frames on bbb, 10 on gop24.
  - Honoured edit list, no B-frames: exact.
  - Ignored edit list (rows 2–4, or players that ignore `elst`): the lead-in
    plays.
  - B-frames: 3 extra frames at the tail even with the edit list honoured.
    `-to` cuts by DTS, so packets with a later PTS slip in. `-t` with the exact
    duration gives 42, and `-frames:v 40` gives 30 visible frames.
- Row 13: the concat demuxer keeps only the first piece's edit list, so the
  second piece's lead-in shows. MP4 output has one edit list entry per track, so
  the edit-list trick can't produce a multi-range cut.

## 3. Multi-call recipe (works)

```bash
# recipe2.sh SRC OUT FMT piece...      (FMT = mp4 or ts for the pieces)
#   enc:A:N  re-encode display frames A..A+N-1 (decode from 0, select by frame number)
#   copy:K:N stream-copy packets K..K+N-1 in decode order (noise bsf drops the rest)
SRC=$1; OUT=$2; FMT=$3; shift 3; i=0; : > list.txt
for p in "$@"; do IFS=: read kind a n <<< "$p"; f=piece$i.$FMT; i=$((i+1)); e=$((a + n - 1))
  if [ $kind = enc ]; then
    ffmpeg -v error -y -i "$SRC" -map 0:v -vf "select=between(n\,$a\,$e)" -fps_mode passthrough \
      -c:v libx264 -preset veryfast -crf 16 -bf 0 $f
  else
    ffmpeg -v error -y -i "$SRC" -map 0:v -c copy -bsf:v "noise=drop=not(between(n\,$a\,$e))" $f
  fi
  echo "file '$PWD/$f'" >> list.txt
done
ffmpeg -v error -y -f concat -safe 0 -i list.txt -map 0:v -c copy "$OUT"
```

I worked out the piece lists by hand from `ffprobe -show_entries packet=pts,dts,flags`:

- bbb [100,200)+[300,400): `enc:100:28 copy:128:72 enc:300:20 copy:320:80`.
  There are no B-frames, so a partial tail GOP can be copied.
- gop24 [10,50)+[100,150): `enc:10:14 copy:24:24 enc:48:2 enc:100:20
  copy:120:24 enc:144:6`. B-frame tails have to be re-encoded.

| output | ff frames (elst / no elst / pkts) | copied bit-exact | re-encoded min PSNR (ff / avf) |
|---|---|---|---|
| bbb recipe2, mp4 or ts pieces | 200 / 200 / 200 | 152/200 (ff and avf) | 44.5 / 43.2 dB |
| bbb **vericut** (`bench/bin/vericut-8b04710`) | 200 / 200 / 200 | 152/200 | 44.5 / 43.2 dB |
| gop24 recipe2 | 90 / 90 / 90 | 48/90 | 46.7 / 47.8 dB |
| gop24 **vericut** | 90 / 90 / 90 | 53/90 | 46.6 / 47.9 dB |

- vericut copies 5 more frames on gop24 because its planner finds the B-frame
  tail frames that are still decodable. I re-encoded those tails wholesale.
- A variant that seeks (`-ss (A-0.5)/fps` for the re-encodes, `-ss K/fps` for
  the copies) gives the same results. The re-encode is exact because input
  seeking decodes from the previous keyframe and discards up to the target
  (row 9). The copy relies on `-ss` landing exactly on keyframe K, so check the
  packet count afterwards.
- Timings on bbb, not rigorous since another job was running: seek variant 0.16 s,
  seek-free variant 0.27–0.31 s, vericut 0.11 s.

What breaks, each tested:

- **SPS/PPS mismatch.** The concat demuxer with `-auto_convert 0` decodes
  64 of 100 frames, at a minimum of 3.5 dB, and AVFoundation fails. With the
  default, SPS/PPS go in-band before each IDR, which is the same as vericut's
  "inband" mode. The final `avcC` is the first piece's (x264 High), followed by
  Baseline SPS in-band at the copied IDRs. Both decoders handle that.
- **Copying a partial tail GOP with B-frames.** `copy:48:2` yields display
  frames 48 and **51**, not 48 and 49, because the packets are in decode order.
  Result: 25/40 exact.
- **B-frames inside a re-encoded head (`-bf 3`).** This was fine: 40 frames,
  copied frames exact.
- **Timestamps.** The concat demuxer rebases each piece, so no edit list or
  negative-DTS problem showed up in either the mp4 or the ts pieces.
- **Planning.** ffmpeg has no way to say "re-encode only what can't be copied".
  The caller has to compute keyframes, the reference/reorder structure and GOP
  closure. That is the part vericut proves.

Comparison with vericut: same execution model (re-encoded pieces plus copied
packets, in-band parameter sets), the same output on these clips, and ffmpeg as
the executor in both. vericut adds the verified plan (`plan_valid`,
`plan_covers`, `plan_copy_copyable`, `copyable_maximal`), which recovers the
extra copyable B-frame tails, and its own muxer. A pure-ffmpeg pipeline would
just move that planning into an unverified script.

## 4. Open-GOP finding (closed-GOP assumption)

Test file: a 4 s `testsrc2` clip encoded with x264 `open-gop=1:keyint=24:bframes=2`.

- Only frame 0 is an IDR (NAL type 5). The I-frames at 24, 48, … are non-IDR
  (type 1), but `stss` lists all 5 of them as sync samples.
- The leading B-frames after each I-frame in decode order reference the previous
  GOP. For example, the packet at decode index 46 is the I-frame at display 48,
  followed by B-frames at display 46 and 47.

vericut (`8b04710`) on this file:
- Cut [46,90): it copies all 44 packets. ffmpeg drops the 2 broken leading
  B-frames and outputs 42 frames, so everything after them is shifted (1/44
  exact). AVFoundation shows 44 frames and the first 2 are garbage (25 dB).
- Cut [40,90): the copied leading B-frames 46 and 47 decode against the
  *re-encoded* frame 45. They come out at 43–50 dB, not bit-exact, even though
  they are counted as "copied".

So `stss` = "decoder reset" is **not** safe for ffmpeg/x264 open-GOP files. A
cheap guard would be to require the copied start to be an IDR, or to check that
no packet after the I-frame in decode order has a lower PTS.

## Reproduce

Use the snippets above. My checker, as a temp script: frame counts via `ffprobe
-count_frames` (with and without `-ignore_editlist 1`), packets via
`-count_packets`, and PSNR with
`[0:v]settb=1/25,setpts=N[o];[1:v]select='…',settb=1/25,setpts=N[r];[o][r]psnr`.

Note: `bench/bench.sh` uses `setpts=N/FRAME_RATE/TB`. That misaligns frames when
the output's guessed frame rate differs from the source's. That happened with
the concatenated recipe outputs here: ffprobe reported 15.36 fps / 384 tbr, and
my first checks showed false 12 dB failures. A constant timebase on both sides avoids it.

For AVFoundation, I decoded with `AVAssetReaderTrackOutput` (420v) and compared
the Y plane with ffmpeg's `extractplanes=y`. Don't use `format=gray`: it
rescales luma. Temp files are deleted.
