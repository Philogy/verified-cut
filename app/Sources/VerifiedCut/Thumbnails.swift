import AVFoundation
import Observation

/// Filmstrip frames per source file, generated once in the background and shared by every lane.
@MainActor
@Observable
final class Thumbnails {
    static let shared = Thumbnails()
    /// Frames per filmstrip, evenly spaced over the whole source.
    static let count = 32

    private(set) var strips: [URL: [CGImage?]] = [:]

    func request(_ url: URL, duration: Double) {
        guard strips[url] == nil else { return }
        strips[url] = Array(repeating: nil, count: Self.count)
        let gen = AVAssetImageGenerator(asset: AVURLAsset(url: url))
        gen.appliesPreferredTrackTransform = true
        gen.maximumSize = CGSize(width: 192, height: 108)
        // Exact frames don't matter for a filmstrip, and nearby keyframes decode far faster.
        let slack = CMTime(seconds: duration / Double(Self.count), preferredTimescale: 600)
        gen.requestedTimeToleranceBefore = slack
        gen.requestedTimeToleranceAfter = slack
        let step = duration / Double(Self.count)
        let times = (0..<Self.count).map { CMTime(seconds: (Double($0) + 0.5) * step, preferredTimescale: 600) }
        Task {
            for await r in gen.images(for: times) {
                guard let img = try? r.image,
                      let i = times.firstIndex(of: r.requestedTime) else { continue }
                strips[url]?[i] = img
            }
        }
    }
}
