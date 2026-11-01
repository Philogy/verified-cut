import AVFoundation
import Foundation
import Observation

/// One clip on the timeline: a source file and a half-open range of display frames.
struct Clip: Identifiable, Equatable {
    let id = UUID()
    let url: URL
    let probe: VeriCut.Probe
    var inFrame: Int
    var outFrame: Int
    /// Lane colour, fixed when the clip is added so it follows the clip when reordered.
    var tint = 0

    static func == (a: Clip, b: Clip) -> Bool {
        a.id == b.id && a.inFrame == b.inFrame && a.outFrame == b.outFrame
    }

    var name: String { url.lastPathComponent }
    var length: Int { outFrame - inFrame }

    /// Seconds spanned by `frames` frames of this clip's source.
    func seconds(_ frames: Int) -> Double {
        Double(frames * probe.frameDuration) / Double(probe.timescale)
    }

    /// Nearest display frame to `t` seconds into the source.
    func frame(at t: Double) -> Int {
        Int((t * Double(probe.timescale) / Double(probe.frameDuration)).rounded())
    }
}

@MainActor
@Observable
final class Timeline {
    var clips: [Clip] = []
    var status: String = "Import clips to begin."
    var planSummary: String = ""
    var busy = false
    var player = AVPlayer()
    /// Output time of the preview player, in seconds.
    var playhead: Double = 0
    var playing = false
    private var timeObserver: Any?
    private var previewGeneration = 0
    private var added = 0

    init() {
        timeObserver = player.addPeriodicTimeObserver(forInterval: CMTime(value: 1, timescale: 30), queue: .main) { [weak self] t in
            MainActor.assumeIsolated {
                self?.playhead = t.seconds
                self?.playing = self?.player.rate != 0
            }
        }
    }

    /// Output start time of each clip, in seconds; the same layout the preview composition uses.
    var starts: [Double] {
        var t = 0.0
        return clips.map { c in defer { t += c.seconds(c.length) }; return t }
    }

    var duration: Double { clips.reduce(0) { $0 + $1.seconds($1.length) } }
    var frameCount: Int { clips.reduce(0) { $0 + $1.length } }

    func seek(to t: Double) {
        playhead = max(0, min(t, duration))
        player.seek(to: CMTime(seconds: playhead, preferredTimescale: 90_000), toleranceBefore: .zero, toleranceAfter: .zero)
    }

    func togglePlay() {
        if player.rate != 0 { player.pause() } else {
            if playhead >= duration - 0.01 { seek(to: 0) }
            player.play()
        }
    }

    func add(_ urls: [URL]) async {
        for url in urls {
            do {
                let p = try await VeriCut.probe(url)
                clips.append(Clip(url: url, probe: p, inFrame: 0, outFrame: p.frameCount, tint: added))
                added += 1
                status = "Added \(url.lastPathComponent): \(p.frameCount) frames, \(p.keyframes.count) keyframes, \(String(format: "%.2f", p.fps)) fps"
            } catch {
                status = "\(url.lastPathComponent): \(error.localizedDescription)"
            }
        }
        await refresh()
    }

    func remove(_ clip: Clip) async {
        clips.removeAll { $0.id == clip.id }
        await refresh()
    }

    func move(from: IndexSet, to: Int) async {
        clips.move(fromOffsets: from, toOffset: to)
        await refresh()
    }

    /// Move clip `id` by `delta` places in the output order.
    func shift(_ id: Clip.ID, by delta: Int) async {
        guard let i = clips.firstIndex(where: { $0.id == id }) else { return }
        let j = i + delta
        guard clips.indices.contains(j) else { return }
        clips.swapAt(i, j)
        await refresh()
    }

    /// Re-plan and rebuild the preview after any edit.
    func refresh() async {
        rebuildPreview()
        guard !clips.isEmpty else { planSummary = ""; return }
        do {
            let plans = try await VeriCut.plan(clips)
            let segs = plans.flatMap(\.segments)
            let copy = segs.filter { $0.kind == "copy" }.reduce(0) { $0 + $1.frames }
            let enc = segs.filter { $0.kind == "encode" }.reduce(0) { $0 + $1.frames }
            planSummary = "Export plan: copy \(copy) frames losslessly, re-encode \(enc)."
        } catch {
            planSummary = error.localizedDescription
        }
    }

    /// Preview only (not verified): an AVMutableComposition of the clip ranges.
    func rebuildPreview() {
        let comp = AVMutableComposition()
        guard let track = comp.addMutableTrack(withMediaType: .video, preferredTrackID: kCMPersistentTrackID_Invalid),
              let audioTrack = comp.addMutableTrack(withMediaType: .audio, preferredTrackID: kCMPersistentTrackID_Invalid)
        else { return }
        let clips = self.clips
        previewGeneration += 1
        let generation = previewGeneration
        Task { @MainActor in
            var cursor = CMTime.zero
            for c in clips {
                let asset = AVURLAsset(url: c.url)
                guard let src = try? await asset.loadTracks(withMediaType: .video).first else { continue }
                let ts = CMTimeScale(c.probe.timescale)
                let d = Int64(c.probe.frameDuration)
                let range = CMTimeRange(start: CMTime(value: Int64(c.inFrame) * d, timescale: ts),
                                        duration: CMTime(value: Int64(c.length) * d, timescale: ts))
                try? track.insertTimeRange(range, of: src, at: cursor)
                if let srcAudio = try? await asset.loadTracks(withMediaType: .audio).first {
                    try? audioTrack.insertTimeRange(range, of: srcAudio, at: cursor)
                }
                cursor = cursor + range.duration
            }
            // Builds overlap while trimming; a slower, older one must not replace a newer preview.
            guard generation == self.previewGeneration else { return }
            // Keep the playhead where it was, so trimming doesn't jump the preview back to 0.
            let t = self.playhead
            self.player.replaceCurrentItem(with: AVPlayerItem(asset: comp))
            self.seek(to: t)
        }
    }

    func export(to url: URL) async {
        busy = true
        defer { busy = false }
        status = "Exporting…"
        do {
            let r = try await VeriCut.export(clips, to: url)
            status = "Exported \(r.frames) frames in \(r.ms) ms: copied \(r.copied) losslessly, re-encoded \(r.reencoded)."
        } catch {
            status = "Export failed: \(error.localizedDescription)"
        }
    }
}
