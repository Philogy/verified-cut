import Foundation

/// Thin wrapper around the Lean `vericut` command-line tool.
/// All planning and muxing happens there; this file only runs it and decodes JSON.
enum VeriCut {
    struct Failure: LocalizedError {
        let message: String
        var errorDescription: String? { message }
    }

    /// Where the Lean binary lives: $VERICUT_BIN, else the Lake build output
    /// next to this source tree (../core/.lake/build/bin/vericut).
    static var binary: URL {
        if let p = ProcessInfo.processInfo.environment["VERICUT_BIN"] {
            return URL(fileURLWithPath: p)
        }
        let here = URL(fileURLWithPath: #filePath)  // app/Sources/VerifiedCut/VeriCut.swift
        return here.deletingLastPathComponent().deletingLastPathComponent()
            .deletingLastPathComponent().deletingLastPathComponent()
            .appendingPathComponent("core/.lake/build/bin/vericut")
    }

    /// GUI apps don't inherit the shell PATH, so look in the usual places.
    static var ffmpeg: String {
        if let p = ProcessInfo.processInfo.environment["FFMPEG"] { return p }
        for p in ["/opt/homebrew/bin/ffmpeg", "/usr/local/bin/ffmpeg"]
        where FileManager.default.isExecutableFile(atPath: p) { return p }
        return "ffmpeg"
    }

    static func run(_ args: [String]) async throws -> Data {
        try await Task.detached {
            let p = Process()
            p.executableURL = binary
            p.arguments = args
            let out = Pipe(), err = Pipe()
            p.standardOutput = out
            p.standardError = err
            do { try p.run() } catch {
                throw Failure(message: "Could not start \(binary.path). Build it with `lake build` in core/. (\(error.localizedDescription))")
            }
            // Read before waiting, so a full pipe can't deadlock the child.
            let data = out.fileHandleForReading.readDataToEndOfFile()
            let errData = err.fileHandleForReading.readDataToEndOfFile()
            p.waitUntilExit()
            guard p.terminationStatus == 0 else {
                let msg = String(decoding: errData, as: UTF8.self).trimmingCharacters(in: .whitespacesAndNewlines)
                throw Failure(message: msg.isEmpty ? "vericut exited with \(p.terminationStatus)" : msg)
            }
            return data
        }.value
    }

    // MARK: probe

    struct Probe: Decodable {
        struct Frame: Decodable {
            let size: Int
            let dur: Int
            let sync: Bool
            let display: Int
        }
        let codec: String
        let timescale: Int
        let frames: [Frame]

        var frameCount: Int { frames.count }
        var frameDuration: Int { frames.first?.dur ?? 1 }
        var fps: Double { Double(timescale) / Double(frameDuration) }
        /// Display positions of keyframes: cuts here need no re-encoding.
        var keyframes: [Int] { frames.filter(\.sync).map(\.display).sorted() }
    }

    static func probe(_ url: URL) async throws -> Probe {
        try JSONDecoder().decode(Probe.self, from: try await run(["probe", url.path]))
    }

    // MARK: plan / export

    struct Segment: Decodable {
        let kind: String
        let frames: Int
    }

    struct ClipPlan: Decodable {
        let path: String
        let segments: [Segment]
    }

    struct Report: Decodable {
        let output: String
        let frames: Int
        let copied: Int
        let reencoded: Int
        let ms: Int
    }

    static func writeTimeline(_ clips: [Clip]) throws -> URL {
        struct T: Encodable {
            struct C: Encodable { let path: String; let `in`: Int; let out: Int }
            let clips: [C]
        }
        let t = T(clips: clips.map { .init(path: $0.url.path, in: $0.inFrame, out: $0.outFrame) })
        let url = FileManager.default.temporaryDirectory
            .appendingPathComponent("verifiedcut-\(UUID().uuidString).json")
        try JSONEncoder().encode(t).write(to: url)
        return url
    }

    static func plan(_ clips: [Clip]) async throws -> [ClipPlan] {
        let tl = try writeTimeline(clips)
        defer { try? FileManager.default.removeItem(at: tl) }
        return try JSONDecoder().decode([ClipPlan].self, from: try await run(["plan", tl.path]))
    }

    /// Export with Apple's hardware H.264 encoder for the boundary frames.
    static func export(_ clips: [Clip], to out: URL, encoder: String = "h264_videotoolbox") async throws -> Report {
        let tl = try writeTimeline(clips)
        defer { try? FileManager.default.removeItem(at: tl) }
        let data = try await run(["export", tl.path, out.path, "--encoder", encoder, "--ffmpeg", ffmpeg])
        return try JSONDecoder().decode(Report.self, from: data)
    }
}
