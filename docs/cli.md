# `vericut` CLI contract

JSON on stdout. On error: a message on stderr and a nonzero exit (1; 2 for bad usage).
Sample counts are per channel. Ranges are half-open `[in, out)`.

| command | output |
|---|---|
| `vericut probe <file.wav\|file.flac>` | `{"sampleRate","channels","bitsPerSample","samples","format":"wav"\|"flac"}` |
| `vericut peaks <file> <buckets>` | `{"min":[…],"max":[…]}`, exactly `buckets` entries each, channel average, in `[-1, 1]` (4 decimals) |
| `vericut export <timeline.json> <out.flac> [--level N]` | `{"samples","bytes","ms"}` |
| `vericut encode <in.wav\|in.flac> <out.flac> [--level N]` | `{"samples","bytes","ms"}` |
| `vericut decode <in.flac> <out.wav>` | `{"samples","bytes","ms"}` |

`timeline.json`: `{"clips":[{"src":"a.wav","in":0,"out":44100}, …]}`. Sources may be WAV or FLAC
and must share sample rate, channels and bit depth (else `clip formats differ: …`).

Input: WAV integer PCM, format 1 or WAVE_FORMAT_EXTENSIBLE (as ffmpeg writes 24-bit and
multichannel), 4–32 bits, 1–8 channels; or FLAC. `probe` exits nonzero on anything `export`
cannot encode (float, A-law, compressed WAVs, more than 8 channels), which the app uses to
decide to convert with ffmpeg first.

`--level` 0–8 roughly follows `flac -N` (block size, partition order, stereo modes); every level
is lossless (`flac_roundTrip_fast`). Levels 3 and up use LPC. Default 8.

WAV output is format 1 up to stereo 16-bit and WAVE_FORMAT_EXTENSIBLE above.
STREAMINFO carries the MD5 of the samples, as libFLAC computes it, so `flac -t` checks it.
