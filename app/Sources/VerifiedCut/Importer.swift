import CryptoKit
import Foundation

/// Brings a file into the project format. WAV/FLAC already in that format are used as they are;
/// anything else is converted by ffmpeg to a WAV in the cache, once. The conversion is outside
/// the verified boundary: from then on the app and `vericut` only see the converted WAV.
enum Importer {
    struct Imported {
        /// The file the timeline refers to and `vericut export` reads.
        let file: URL
        let probe: VeriCut.Probe
        /// Set when `file` is an ffmpeg conversion of the file the user picked.
        let convertedFrom: URL?
    }

    /// GUI apps don't inherit the shell PATH, so look in the usual places.
    static var ffmpeg: URL {
        if let p = ProcessInfo.processInfo.environment["FFMPEG"] { return URL(fileURLWithPath: p) }
        for p in ["/opt/homebrew/bin/ffmpeg", "/usr/local/bin/ffmpeg"]
        where FileManager.default.isExecutableFile(atPath: p) { return URL(fileURLWithPath: p) }
        return URL(fileURLWithPath: "/usr/bin/env")
    }

    static var cache: URL {
        let dir = FileManager.default.urls(for: .cachesDirectory, in: .userDomainMask)[0]
            .appendingPathComponent("VerifiedCut/imports", isDirectory: true)
        try? FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        return dir
    }

    /// `project` is the format every clip must share; nil for the first clip, which then sets it:
    /// its own format if `vericut` reads it, else `Format.fallback`.
    static func prepare(_ url: URL, project: VeriCut.Format?) async throws -> Imported {
        let native = ["wav", "flac"].contains(url.pathExtension.lowercased())
        // vericut reads integer PCM WAV and FLAC only; e.g. float WAVs fail here and get converted.
        if native, let p = try? await VeriCut.probe(url) {
            if project == nil || p.audioFormat == project { return Imported(file: url, probe: p, convertedFrom: nil) }
        }
        let target = project ?? .fallback
        let out = try await convert(url, to: target)
        return Imported(file: out, probe: try await VeriCut.probe(out), convertedFrom: url)
    }

    private static func convert(_ url: URL, to f: VeriCut.Format) async throws -> URL {
        let attrs = try FileManager.default.attributesOfItem(atPath: url.path)
        let stamp = "\(url.path)|\(attrs[.size] ?? 0)|\((attrs[.modificationDate] as? Date)?.timeIntervalSince1970 ?? 0)|\(f)"
        let key = SHA256.hash(data: Data(stamp.utf8)).prefix(8).map { String(format: "%02x", $0) }.joined()
        let out = cache.appendingPathComponent("\(url.deletingPathExtension().lastPathComponent)-\(key).wav")
        if FileManager.default.fileExists(atPath: out.path) { return out }
        let codec = [8: "pcm_u8", 24: "pcm_s24le", 32: "pcm_s32le"][f.bitsPerSample] ?? "pcm_s16le"
        let tmp = out.deletingPathExtension().appendingPathExtension("part.wav")
        var args = ["-v", "error", "-y", "-i", url.path, "-map", "0:a:0", "-ar", String(f.sampleRate),
                    "-ac", String(f.channels), "-c:a", codec,
                    // Plain PCM header: no LIST/INFO chunks or WAVE_FORMAT_EXTENSIBLE for a minimal WAV reader.
                    "-map_metadata", "-1", "-rf64", "never", tmp.path]
        if ffmpeg.lastPathComponent == "env" { args.insert("ffmpeg", at: 0) }
        _ = try await Process.output(ffmpeg, args, notFound: "Install ffmpeg (brew install ffmpeg) to import this file.")
        try FileManager.default.moveItem(at: tmp, to: out)
        return out
    }
}
