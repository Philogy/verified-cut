// swift-tools-version:6.0
import PackageDescription

let package = Package(
    name: "VerifiedCut",
    // macOS 15 for onScrollGeometryChange: lanes draw only the visible part of their waveform.
    platforms: [.macOS(.v15)],
    targets: [
        // Swift 5 mode: the code predates strict concurrency checking.
        .executableTarget(name: "VerifiedCut", path: "Sources/VerifiedCut", swiftSettings: [.swiftLanguageMode(.v5)])
    ]
)
