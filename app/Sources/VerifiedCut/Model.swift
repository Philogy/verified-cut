import AVFoundation
import Foundation
import Observation

/// One clip on the timeline: a source file and a half-open range of display frames.
struct Clip: Identifiable, Equatable {
    let id = UUID()
    let url: URL
    let probe: SmartCut.Probe
    var inFrame: Int
    var outFrame: Int

    static func == (a: Clip, b: Clip) -> Bool {
        a.id == b.id && a.inFrame == b.inFrame && a.outFrame == b.outFrame
    }

    var name: String { url.lastPathComponent }
    var length: Int { outFrame - inFrame }
}

@MainActor
@Observable
final class Timeline {
    var clips: [Clip] = []
    var status: String = "Import clips to begin."
    var planSummary: String = ""
    var busy = false
    var player = AVPlayer()

    func add(_ urls: [URL]) async {
        for url in urls {
            do {
                let p = try await SmartCut.probe(url)
                clips.append(Clip(url: url, probe: p, inFrame: 0, outFrame: p.frameCount))
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

    /// Re-plan and rebuild the preview after any edit.
    func refresh() async {
        rebuildPreview()
        guard !clips.isEmpty else { planSummary = ""; return }
        do {
            let plans = try await SmartCut.plan(clips)
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
        guard let track = comp.addMutableTrack(withMediaType: .video, preferredTrackID: kCMPersistentTrackID_Invalid) else { return }
        let clips = self.clips
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
                cursor = cursor + range.duration
            }
            self.player.replaceCurrentItem(with: AVPlayerItem(asset: comp))
        }
    }

    func export(to url: URL) async {
        busy = true
        defer { busy = false }
        status = "Exporting…"
        do {
            let r = try await SmartCut.export(clips, to: url)
            status = "Exported \(r.frames) frames in \(r.ms) ms: copied \(r.copied) losslessly, re-encoded \(r.reencoded)."
        } catch {
            status = "Export failed: \(error.localizedDescription)"
        }
    }
}
