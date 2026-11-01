import Foundation

/// Thin wrapper around the Lean `vericut` command-line tool (contract: docs/cli.md).
/// Decoding, splicing and FLAC encoding happen there; this file only runs it and decodes JSON.
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

    static func run(_ args: [String]) async throws -> Data {
        try await Process.output(binary, args, notFound: "Build it with `lake build` in core/.")
    }

    // MARK: probe

    /// Sample rate, channel count and bit depth: clips can only be spliced if these match.
    struct Format: Hashable, CustomStringConvertible {
        let sampleRate: Int
        let channels: Int
        let bitsPerSample: Int

        static let fallback = Format(sampleRate: 44_100, channels: 2, bitsPerSample: 16)

        var description: String {
            let khz = Double(sampleRate) / 1000
            let rate = khz == khz.rounded() ? String(Int(khz)) : String(format: "%.1f", khz)
            let ch = channels == 1 ? "mono" : channels == 2 ? "stereo" : "\(channels) ch"
            return "\(rate) kHz · \(bitsPerSample)-bit · \(ch)"
        }
    }

    struct Probe: Decodable {
        let sampleRate: Int
        let channels: Int
        let bitsPerSample: Int
        /// Per channel, i.e. sample frames.
        let samples: Int
        let format: String

        var audioFormat: Format { Format(sampleRate: sampleRate, channels: channels, bitsPerSample: bitsPerSample) }
    }

    static func probe(_ url: URL) async throws -> Probe {
        try JSONDecoder().decode(Probe.self, from: try await run(["probe", url.path]))
    }

    // MARK: peaks

    /// Per-bucket minimum and maximum of the mono mix, in [-1, 1].
    struct Peaks: Decodable {
        let min: [Float]
        let max: [Float]
    }

    static func peaks(_ url: URL, buckets: Int) async throws -> Peaks {
        try JSONDecoder().decode(Peaks.self, from: try await run(["peaks", url.path, String(buckets)]))
    }

    // MARK: export

    struct Report: Decodable {
        let samples: Int
        let bytes: Int
        let ms: Int
    }

    static func writeTimeline(_ clips: [Clip]) throws -> URL {
        struct T: Encodable {
            struct C: Encodable { let src: String; let `in`: Int; let out: Int }
            let clips: [C]
        }
        let t = T(clips: clips.map { .init(src: $0.file.path, in: $0.inSample, out: $0.outSample) })
        let url = FileManager.default.temporaryDirectory
            .appendingPathComponent("verifiedcut-\(UUID().uuidString).json")
        try JSONEncoder().encode(t).write(to: url)
        return url
    }

    static func export(_ clips: [Clip], to out: URL, level: Int) async throws -> Report {
        let tl = try writeTimeline(clips)
        defer { try? FileManager.default.removeItem(at: tl) }
        let data = try await run(["export", tl.path, out.path, "--level", String(level)])
        return try JSONDecoder().decode(Report.self, from: data)
    }
}

extension Process {
    /// Run `exe args` off the main thread; stdout on success, stderr as the error otherwise.
    static func output(_ exe: URL, _ args: [String], notFound: String) async throws -> Data {
        try await Task.detached {
            let p = Process()
            p.executableURL = exe
            p.arguments = args
            let out = Pipe(), err = Pipe()
            p.standardOutput = out
            p.standardError = err
            do { try p.run() } catch {
                throw VeriCut.Failure(message: "Could not start \(exe.path). \(notFound) (\(error.localizedDescription))")
            }
            // Drain stderr concurrently and stdout here, so neither pipe can fill up and block the child.
            let errData = Task.detached { err.fileHandleForReading.readDataToEndOfFile() }
            let data = out.fileHandleForReading.readDataToEndOfFile()
            let errBytes = await errData.value
            p.waitUntilExit()
            guard p.terminationStatus == 0 else {
                let msg = String(decoding: errBytes, as: UTF8.self).trimmingCharacters(in: .whitespacesAndNewlines)
                throw VeriCut.Failure(message: msg.isEmpty ? "\(exe.lastPathComponent) exited with \(p.terminationStatus)" : msg)
            }
            return data
        }.value
    }
}
