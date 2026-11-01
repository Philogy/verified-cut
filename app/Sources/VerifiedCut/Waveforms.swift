import Foundation
import Observation

/// Waveform peaks per source file, from `vericut peaks`, fetched once and shared by every lane.
@MainActor
@Observable
final class Waveforms {
    static let shared = Waveforms()

    private(set) var peaks: [URL: VeriCut.Peaks] = [:]
    private var pending: Set<URL> = []

    /// About 32 samples per bucket, which stays finer than a point up to the maximum zoom;
    /// capped so an hour-long podcast is still a ~2 MB answer.
    static func buckets(for samples: Int) -> Int { min(max(samples / 32, 1), 100_000) }

    func request(_ url: URL, samples: Int) {
        guard peaks[url] == nil, !pending.contains(url) else { return }
        pending.insert(url)
        Task {
            defer { pending.remove(url) }
            if let p = try? await VeriCut.peaks(url, buckets: Self.buckets(for: samples)) { peaks[url] = p }
        }
    }
}
