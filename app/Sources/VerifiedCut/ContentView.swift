import AppKit
import AVKit
import SwiftUI
import UniformTypeIdentifiers

struct ContentView: View {
    @State private var timeline = Timeline()
    @State private var importing = false

    var body: some View {
        HSplitView {
            VStack(spacing: 0) {
                List {
                    ForEach($timeline.clips) { $clip in
                        ClipRow(clip: $clip,
                                onCommit: { Task { await timeline.refresh() } },
                                onRemove: { Task { await timeline.remove(clip) } })
                    }
                    .onMove { from, to in Task { await timeline.move(from: from, to: to) } }
                }
                Divider()
                HStack {
                    Button("Import…") { importing = true }
                    Spacer()
                    Text(timeline.planSummary).font(.callout).foregroundStyle(.secondary)
                    Spacer()
                    Button("Export…") { chooseExport() }
                        .keyboardShortcut("e")
                        .disabled(timeline.clips.isEmpty || timeline.busy)
                }
                .padding(10)
            }
            .frame(minWidth: 420)

            VStack(spacing: 0) {
                VideoPlayer(player: timeline.player)
                Divider()
                Text(timeline.status)
                    .font(.callout)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(10)
            }
            .frame(minWidth: 400)
        }
        .fileImporter(isPresented: $importing,
                      allowedContentTypes: [.mpeg4Movie, .quickTimeMovie],
                      allowsMultipleSelection: true) { result in
            if case .success(let urls) = result {
                Task { await timeline.add(urls) }
            }
        }
    }

    private func chooseExport() {
        let panel = NSSavePanel()
        panel.allowedContentTypes = [.mpeg4Movie]
        panel.nameFieldStringValue = "export.mp4"
        if panel.runModal() == .OK, let url = panel.url {
            Task { await timeline.export(to: url) }
        }
    }
}
