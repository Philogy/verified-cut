#!/usr/bin/env bash
# Recreate the sample clips used by the tests.
#   bbb_baseline.mp4   Big Buck Bunny, 60 s, H.264 Constrained Baseline, no B-frames, 23 keyframes
#   bear_bframes.mp4   Chromium media test clip, H.264 High with B-frames, one keyframe
#   prores_intra.mov   synthetic ProRes 422 Proxy, every frame a keyframe
#   gop30_nob.mp4      synthetic H.264, keyframe every 30 frames, no B-frames
#   gop24_bframes.mp4  synthetic H.264, keyframe every 24 frames, 2 B-frames
set -euo pipefail
cd "$(dirname "$0")"
curl -sSfL -o bbb_baseline.mp4 https://raw.githubusercontent.com/mediaelement/mediaelement-files/master/big_buck_bunny.mp4
curl -sSfL -o bear_bframes.mp4 https://raw.githubusercontent.com/chromium/chromium/main/media/test/data/bear-1280x720.mp4
src=(-f lavfi -i testsrc2=size=640x360:rate=30)
ffmpeg -v error -y "${src[@]}" -t 4 -c:v prores_ks -profile:v 0 prores_intra.mov
ffmpeg -v error -y "${src[@]}" -t 6 -c:v libx264 -pix_fmt yuv420p -bf 0 \
  -x264-params keyint=30:min-keyint=30:scenecut=0 gop30_nob.mp4
ffmpeg -v error -y "${src[@]}" -t 6 -c:v libx264 -pix_fmt yuv420p -bf 2 \
  -x264-params keyint=24:min-keyint=24:scenecut=0 gop24_bframes.mp4
ls -la
