import AppKit
import AVKit
import SwiftUI
import UniformTypeIdentifiers

struct ContentView: View {
    @State private var timeline = Timeline()
    @State private var importing = false

    var body: some View {
        VSplitView {
            VideoPlayer(player: timeline.player)
                // VideoPlayer drops the identifier unless it gets its own container element.
                .accessibilityElement(children: .contain)
                .accessibilityIdentifier("preview.player")
                .background(.black)
                .frame(minHeight: 240, idealHeight: 420)
            VStack(spacing: 0) {
                toolbar
                Divider()
                TimelineEditor(timeline: timeline)
                ZStack {
                    Divider()
                    if timeline.busy {
                        BusyBar()
                            .accessibilityElement()
                            .accessibilityLabel("Exporting")
                            .accessibilityIdentifier("export.progress")
                            .transition(.opacity)
                    }
                }
                .animation(.easeInOut(duration: 0.2), value: timeline.busy)
                Text(timeline.status)
                    .font(.callout).foregroundStyle(.secondary)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(.horizontal, 10).padding(.vertical, 6)
                    .accessibilityIdentifier("status")
            }
            .frame(minHeight: 220, idealHeight: 300)
        }
        .background(Color(white: 0.11))
        .fileImporter(isPresented: $importing,
                      allowedContentTypes: [.mpeg4Movie, .quickTimeMovie],
                      allowsMultipleSelection: true) { result in
            if case .success(let urls) = result {
                Task { await timeline.add(urls) }
            }
        }
    }

    private var toolbar: some View {
        HStack(spacing: 12) {
            Button { importing = true } label: { Label("Import…", systemImage: "plus") }
                .accessibilityIdentifier("import")
            Button { timeline.togglePlay() } label: {
                Image(systemName: timeline.playing ? "pause.fill" : "play.fill").frame(width: 16)
            }
            .keyboardShortcut(.space, modifiers: [])
            .disabled(timeline.clips.isEmpty)
            .accessibilityIdentifier("transport.play")
            Text("\(timecode(timeline.playhead)) / \(timecode(timeline.duration))")
                .font(.callout.monospacedDigit())
                .accessibilityIdentifier("transport.time")
            Text("\(timeline.frameCount) frames")
                .font(.callout.monospacedDigit()).foregroundStyle(.secondary)
                .accessibilityIdentifier("timeline.frames")
            Spacer()
            Text(timeline.planSummary).font(.callout).foregroundStyle(.secondary)
                .accessibilityIdentifier("plan.summary")
            Spacer()
            Button { chooseExport() } label: { Label("Export…", systemImage: "square.and.arrow.up") }
                .keyboardShortcut("e")
                .buttonStyle(.borderedProminent)
                .disabled(timeline.clips.isEmpty || timeline.busy)
                .accessibilityIdentifier("export")
        }
        .padding(.horizontal, 10).padding(.vertical, 7)
        .background(Color(white: 0.16))
    }

    private func chooseExport() {
        guard !timeline.busy else { return }
        let panel = NSSavePanel()
        panel.allowedContentTypes = [.mpeg4Movie]
        panel.nameFieldStringValue = "export.mp4"
        if panel.runModal() == .OK, let url = panel.url {
            Task { await timeline.export(to: url) }
        }
    }
}

/// Indeterminate progress: a short accent segment gliding back and forth along a 2pt track.
struct BusyBar: View {
    @State private var right = false

    var body: some View {
        GeometryReader { geo in
            let w = geo.size.width * 0.18
            Capsule()
                .fill(Color.accentColor.opacity(0.85))
                .frame(width: w)
                .offset(x: right ? geo.size.width - w : 0)
        }
        .frame(height: 2)
        .background(Color.white.opacity(0.06))
        .onAppear {
            withAnimation(.easeInOut(duration: 1.1).repeatForever(autoreverses: true)) { right = true }
        }
    }
}
