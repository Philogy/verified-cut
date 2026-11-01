import Foundation
import UserNotifications

/// Posts "export finished" notifications.
/// UNUserNotificationCenter traps without a bundle identifier, which is the case under
/// `swift run`, so there (and if notifications are refused) we go through osascript instead.
@MainActor
enum Notifier {
    private static var authorized: Bool?
    private static let delegate = Delegate()

    /// Show banners even while the app is frontmost, which it usually is when an export ends.
    private final class Delegate: NSObject, UNUserNotificationCenterDelegate {
        func userNotificationCenter(_ center: UNUserNotificationCenter, willPresent notification: UNNotification,
                                    withCompletionHandler completionHandler: @escaping (UNNotificationPresentationOptions) -> Void) {
            completionHandler([.banner, .sound])
        }
    }

    static func post(title: String, body: String) async {
        guard Bundle.main.bundleIdentifier != nil else { return osascript(title: title, body: body) }
        let center = UNUserNotificationCenter.current()
        if authorized == nil {
            center.delegate = delegate
            // Ad-hoc signed builds (swift build, the Tart VM bundle) get UNError.notificationsNotAllowed here.
            authorized = (try? await center.requestAuthorization(options: [.alert, .sound])) ?? false
        }
        guard authorized == true else { return osascript(title: title, body: body) }
        let content = UNMutableNotificationContent()
        content.title = title
        content.body = body
        content.sound = .default
        do {
            try await center.add(UNNotificationRequest(identifier: UUID().uuidString, content: content, trigger: nil))
        } catch {
            osascript(title: title, body: body)
        }
    }

    private static func osascript(title: String, body: String) {
        let p = Process()
        p.executableURL = URL(fileURLWithPath: "/usr/bin/osascript")
        // Passed as argv rather than spliced into the script, so quotes in file names are harmless.
        p.arguments = ["-e", "on run argv", "-e", "display notification (item 2 of argv) with title (item 1 of argv)",
                       "-e", "end run", title, body]
        try? p.run()
    }
}

