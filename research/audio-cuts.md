# Cutting AAC audio without re-encoding

How vericut keeps the source audio in sync with a cut video, and why it copies
packets instead of re-encoding the edges.

## How AAC packets behave at a cut

- **One packet is 1024 PCM samples** (AAC-LC) and decodes through a 2048-point
  MDCT with 50 % overlap. The samples of packet *k* are the overlap-add of
  packet *k*'s inverse transform and packet *k − 1*'s. A packet decoded without
  its predecessor gives wrong output for its 1024 samples. [1][2]
- **Pre-roll.** MP4 marks this with a `roll` sample group (`sgpd`/`sbgp`) with
  `roll_distance = −1`: decode one packet before the one you want. Apple's
  explicit-delay example writes exactly this (`sgpd` version 1, `roll`, one
  entry, −1; `sbgp` mapping every packet to it). ISO/IEC 14496-12:2022
  deprecates negative distances, but files still carry −1. [2][3]
- **Priming / encoder delay.** Encoders emit extra samples at the start (2112
  classically, 1024 for ffmpeg's encoder). The edit list's `media_time` points
  at the first sample to play; the edit's duration excludes the priming and
  the remainder at the end. [1][2][4]
- **Apple's fallback.** If a track has no `roll` sample group, Apple readers
  assume the historical implicit 2112-sample delay. [1][2] Measured: AVFoundation
  plays Big Buck Bunny and the NASA CRS-23 clip (no `roll` group) 2112 samples
  shorter than their packets; it plays our output (with a `roll` group) exactly
  by its edit list.
- **ffmpeg** trims sample-exactly at the *first* edit (`skip_samples` side
  data); later edits only drop whole packets, so a partial packet at a splice
  plays whole. [5] Measured on a 3-cut Big Buck Bunny export: the 2nd and 3rd
  cuts start 544 and 480 samples (at 22.05 kHz) late in ffmpeg, not cumulatively.

## The scheme

Copy, never re-encode, and trim with the edit list:

1. Per cut, the source sample that plays with the clip's first frame is read
   off both tracks' edit lists (`alignedSample`, `Main.lean`).
2. The cut's length in samples is `sampleAt(end) − sampleAt(start)` on the
   **output** video clock (nearest sample), so lengths telescope: cut *i*
   starts within half a sample of its video for every *i*, however many cuts.
3. Copy the packets covering the cut **plus one before** (the pre-roll). The
   splice into the previous cut's packets lands in the pre-roll, whose output
   is never presented; every presented packet is decoded after its true
   predecessor, so it decodes exactly as in the source.
4. One edit per cut: `media_time` = where the cut's first sample is in the
   output media, duration = its length. Empty edits fill time where a source
   has no audio (or a cut starts before the source's first full packet).
5. Write a `roll` group (−1) so Apple readers honour the edit list instead of
   assuming 2112 samples of priming, and make the movie timescale the lcm of
   the media timescales, so every edit is a whole number of samples.

This is proven for every decoder of that shape (`AudioCodec`:
samples = f(previous packet, packet)): `exportAudio_exact` (the output plays
exactly the source samples), `exportAudio_synced` (half-sample sync,
no drift), `exportAudio_aligned`.

**Why not re-encode the edge packets?** A re-encoded edge still ends next to a
copied packet whose decode depends on the packet before it, which is now a
different (re-encoded) one: the splice artefact moves, it doesn't go away, and
the output is only approximately the source. Copying with a pre-roll is exact
and costs no encode. The price is that the player must honour a multi-entry
edit list; QuickTime/AVFoundation does (tested, `AudioTests`).

## skeskinen/smartcut

`PassthruAudioCutter` (`cut_video.py`) copies the packets whose pts falls in
`[start, end)` of each segment (`np.searchsorted`), shifts their timestamps by
the segment's output offset, and bumps any non-increasing pts/dts by one. It
writes no edit list and no pre-roll, so:

- each cut starts on a packet boundary: up to one packet (≈21 ms at 48 kHz)
  early or late against the video, and its length is whole packets;
- the first packet after every splice is decoded after the wrong predecessor
  (an MDCT-overlap glitch of one packet);
- segment offsets are exact `Fraction`s, so the error doesn't accumulate.

vericut is sample-exact on the same files: on the CRS-23 bench timeline
(3 cuts, 3,363,360 samples), every sample equals the source's.

## Sources

1. Apple, QuickTime File Format, *Audio priming: handling encoder delay in AAC*,
   https://developer.apple.com/documentation/quicktime-file-format/appendix_g_audio_priming_handling_encoder_delay_in_aac
2. Apple, *Using track structures to represent encoder delay explicitly*, and the
   worked example, https://developer.apple.com/documentation/quicktime-file-format/using_track_structures_to_represent_encode_delay_explictly ,
   https://developer.apple.com/documentation/quicktime-file-format/example_representing_encoder_delay_explicitly
3. ffmpeg-devel, Aug 2017, `sgpd`/`sbgp` roll patch discussion,
   https://ffmpeg.org/pipermail/ffmpeg-devel/2017-August/214567.html ; Xiph,
   Opus in ISOBMFF (roll_distance notes),
   https://gitlab.xiph.org/xiph/opus/-/commit/32ff38bc8a3f1eba8cd27721cf4ce834ad12f9ad.diff
4. Apple, *Historical solution for implicit encoder delay*,
   https://developer.apple.com/documentation/quicktime-file-format/historical_solution_implicit_encoder_delay
5. ffmpeg-devel, Sep 2016, mov edit-list patches (`mov_fix_index`, skip samples),
   https://ffmpeg.org/pipermail/ffmpeg-devel/2016-September/199975.html ,
   https://ffmpeg.org/pipermail/ffmpeg-devel/2016-September/199816.html

The MDCT-overlap description is partly from background knowledge (the search
summaries say so); the ISO text is paywalled and was not read. The behaviour
that matters here (exact decode after one pre-roll packet; AVFoundation and
ffmpeg edit-list handling) was measured, not taken from these sources.
