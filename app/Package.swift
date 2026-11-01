// swift-tools-version:5.9
import PackageDescription

let package = Package(
    name: "VerifiedCut",
    platforms: [.macOS(.v14)],
    targets: [
        // SwiftUI's VideoPlayer needs AVKit itself, which SwiftPM doesn't autolink.
        .executableTarget(name: "VerifiedCut", path: "Sources/VerifiedCut",
                          linkerSettings: [.linkedFramework("AVKit")])
    ]
)
