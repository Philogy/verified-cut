import AVFoundation
import Foundation
import Observation

/// One clip on the timeline: a source file and a half-open range of sample frames.
struct Clip: Identifiable, Equatable {
    let id = UUID()
    /// What `vericut` reads: the picked file, or its ffmpeg conversion to the project format.
    let file: URL
    let probe: VeriCut.Probe
    /// The file the user picked, if it had to be converted on import.
    let convertedFrom: URL?
    var inSample: Int
    var outSample: Int
    /// Lane colour, fixed when the clip is added so it follows the clip when reordered.
    var tint = 0

    static func == (a: Clip, b: Clip) -> Bool {
        a.id == b.id && a.inSample == b.inSample && a.outSample == b.outSample
    }

    var name: String { (convertedFrom ?? file).lastPathComponent }
    var length: Int { outSample - inSample }

    func seconds(_ samples: Int) -> Double { Double(samples) / Double(probe.sampleRate) }

    /// Nearest sample frame to `t` seconds into the source.
    func sample(at t: Double) -> Int { Int((t * Double(probe.sampleRate)).rounded()) }
}

@MainActor
@Observable
final class Timeline {
    var clips: [Clip] = []
    var status: String = "Import audio to begin."
    var busy = false
    /// FLAC compression level passed to `vericut export`.
    var level = 5
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

    /// Every clip shares this format (the first clip's); imports are converted to it.
    var format: VeriCut.Format? { clips.first?.probe.audioFormat }

    /// Output start time of each clip, in seconds; the same layout the preview composition uses.
    var starts: [Double] {
        var t = 0.0
        return clips.map { c in defer { t += c.seconds(c.length) }; return t }
    }

    var duration: Double { clips.reduce(0) { $0 + $1.seconds($1.length) } }
    var sampleCount: Int { clips.reduce(0) { $0 + $1.length } }

    func seek(to t: Double) {
        playhead = max(0, min(t, duration))
        player.seek(to: CMTime(seconds: playhead, preferredTimescale: 192_000), toleranceBefore: .zero, toleranceAfter: .zero)
    }

    func togglePlay() {
        if player.rate != 0 { player.pause() } else {
            if playhead >= duration - 0.01 { seek(to: 0) }
            player.play()
        }
    }

    func add(_ urls: [URL]) async {
        for url in urls {
            status = "Importing \(url.lastPathComponent)…"
            do {
                let im = try await Importer.prepare(url, project: format)
                let p = im.probe
                clips.append(Clip(file: im.file, probe: p, convertedFrom: im.convertedFrom,
                                  inSample: 0, outSample: p.samples, tint: added))
                added += 1
                let how = im.convertedFrom == nil ? "" : " (converted with ffmpeg)"
                status = "Added \(url.lastPathComponent)\(how): \(p.samples) samples, \(p.audioFormat)"
            } catch {
                status = "\(url.lastPathComponent): \(error.localizedDescription)"
            }
        }
        refresh()
    }

    func remove(_ clip: Clip) {
        clips.removeAll { $0.id == clip.id }
        refresh()
    }

    /// Move clip `id` by `delta` places in the output order.
    func shift(_ id: Clip.ID, by delta: Int) {
        guard let i = clips.firstIndex(where: { $0.id == id }) else { return }
        let j = i + delta
        guard clips.indices.contains(j) else { return }
        clips.swapAt(i, j)
        refresh()
    }

    /// Rebuild the preview after any edit. Preview only (not verified): an AVMutableComposition
    /// of the clip ranges, timed in samples.
    func refresh() {
        let comp = AVMutableComposition()
        let clips = self.clips
        previewGeneration += 1
        let generation = previewGeneration
        Task { @MainActor in
            var cursor = CMTime.zero
            for c in clips {
                let rate = CMTimeScale(c.probe.sampleRate)
                let range = CMTimeRange(start: CMTime(value: Int64(c.inSample), timescale: rate),
                                        duration: CMTime(value: Int64(c.length), timescale: rate))
                // Whole-asset insert: on macOS 26 AVMutableCompositionTrack.insertTimeRange fails
                // with -11800 (-12780) for every source we tried, WAV, FLAC and MP4 alike.
                try? await comp.insertTimeRange(range, of: AVURLAsset(url: c.file), at: cursor)
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
        let clock = ContinuousClock()
        let start = clock.now
        let want = sampleCount
        do {
            let r = try await VeriCut.export(clips, to: url, level: level)
            let elapsed = (clock.now - start).formatted(.units(allowed: [.minutes, .seconds], width: .abbreviated, fractionalPart: .show(length: 1)))
            let size = ByteCountFormatter.string(fromByteCount: Int64(r.bytes), countStyle: .file)
            let check = r.samples == want ? "" : " — expected \(want) samples!"
            status = "Exported \(r.samples) samples (\(timecode(Double(r.samples) / Double(format?.sampleRate ?? 1)))) to \(url.lastPathComponent), \(size), level \(level), in \(r.ms) ms\(check)"
            // Not awaited: a pending permission prompt must not keep the export button disabled.
            Task { await Notifier.post(title: "Export finished", body: "\(url.lastPathComponent) · \(size) · \(elapsed)") }
        } catch {
            status = "Export failed: \(error.localizedDescription)"
            let message = "\(url.lastPathComponent): \(error.localizedDescription.prefix(200))"
            Task { await Notifier.post(title: "Export failed", body: message) }
        }
    }
}
