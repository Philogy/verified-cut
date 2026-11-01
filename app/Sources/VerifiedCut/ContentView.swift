import AppKit
import SwiftUI
import UniformTypeIdentifiers

struct ContentView: View {
    @State private var timeline = Timeline()
    @State private var importing = false

    var body: some View {
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
        .background(Color(white: 0.11))
        // Anything ffmpeg reads; non-WAV/FLAC files are converted on import (Importer).
        .fileImporter(isPresented: $importing, allowedContentTypes: [.audio], allowsMultipleSelection: true) { result in
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
            Text("\(timeline.sampleCount) samples")
                .font(.callout.monospacedDigit()).foregroundStyle(.secondary)
                .accessibilityIdentifier("timeline.samples")
            Spacer()
            if let f = timeline.format {
                Text(f.description).font(.callout).foregroundStyle(.secondary)
                    .help("Project format, set by the first clip. Other imports are converted to it with ffmpeg.")
                    .accessibilityIdentifier("project.format")
            }
            Spacer()
            Picker("Level", selection: $timeline.level) {
                ForEach(0...8, id: \.self) { Text("\($0)").tag($0) }
            }
            .fixedSize()
            .help("FLAC compression level: higher is smaller and slower to encode, never lossy")
            .accessibilityIdentifier("export.level")
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
        panel.allowedContentTypes = [UTType(filenameExtension: "flac") ?? .audio]
        panel.nameFieldStringValue = "export.flac"
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
