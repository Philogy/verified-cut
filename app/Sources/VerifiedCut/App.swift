import AppKit
import SwiftUI

@main
struct VerifiedCutApp: App {
    init() {
        // A SwiftPM executable is not a bundled .app: make it a regular,
        // frontmost app so the window and menu bar behave normally.
        NSApplication.shared.setActivationPolicy(.regular)
        NSApplication.shared.activate(ignoringOtherApps: true)
    }

    var body: some Scene {
        WindowGroup("Verified Cut") {
            ContentView()
                .frame(minWidth: 900, minHeight: 600)
                .preferredColorScheme(.dark)
        }
    }
}
