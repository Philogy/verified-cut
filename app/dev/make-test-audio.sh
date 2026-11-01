#!/bin/sh
# Synthetic clips for trying the app against the stub: samples/synth/ (untracked).
set -eu
cd "$(dirname "$0")/../../samples" && mkdir -p synth && cd synth
F=${FFMPEG:-ffmpeg}
"$F" -v error -y -f lavfi -i "sine=frequency=440:sample_rate=44100:duration=4,volume=6" -ac 2 -c:a pcm_s16le tone440.wav
"$F" -v error -y -f lavfi -i "anoisesrc=color=pink:sample_rate=44100:duration=3:amplitude=0.5,afade=t=in:d=1,afade=t=out:st=2:d=1" -ac 2 -c:a pcm_s16le noise.wav
"$F" -v error -y -f lavfi -i "sine=frequency=220:sample_rate=44100:duration=5,volume=5,tremolo=f=2:d=0.9" -ac 2 -c:a flac -sample_fmt s16 chord16.flac
# Formats the app has to convert on import: 48 kHz/24-bit/mono WAV and an MP3.
"$F" -v error -y -f lavfi -i "sine=frequency=660:sample_rate=48000:duration=2,volume=6" -ac 1 -c:a pcm_s24le mono48k24.wav
"$F" -v error -y -f lavfi -i "sine=frequency=330:sample_rate=44100:duration=3,volume=6" -c:a libmp3lame -q:a 2 beep.mp3
ls -l
