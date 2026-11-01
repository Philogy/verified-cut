import SwiftUI

/// One clip: name, in/out controls, and a strip showing where keyframes are.
/// Cutting the in point on a keyframe means nothing needs re-encoding.
struct ClipRow: View {
    @Binding var clip: Clip
    var onCommit: () -> Void
    var onRemove: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text(clip.name).font(.headline)
                    .accessibilityIdentifier("clip.name")
                Spacer()
                Text("\(clip.length) frames · \(timecode(clip.length))")
                    .font(.caption).foregroundStyle(.secondary)
                    .accessibilityIdentifier("clip.length")
                Button(role: .destructive, action: onRemove) { Image(systemName: "trash") }
                    .buttonStyle(.borderless)
                    .accessibilityIdentifier("clip.remove")
            }
            KeyframeStrip(clip: clip)
                .frame(height: 14)
                .accessibilityIdentifier("clip.keyframes")
            frameControl("In", id: "clip.in", value: $clip.inFrame, range: 0...(clip.outFrame - 1))
            frameControl("Out", id: "clip.out", value: $clip.outFrame, range: (clip.inFrame + 1)...clip.probe.frameCount)
        }
        .padding(.vertical, 4)
    }

    private func frameControl(_ label: String, id: String, value: Binding<Int>, range: ClosedRange<Int>) -> some View {
        HStack {
            Text(label).frame(width: 28, alignment: .leading)
            Slider(value: Binding(get: { Double(value.wrappedValue) },
                                  set: { value.wrappedValue = Int($0.rounded()) }),
                   in: Double(range.lowerBound)...Double(max(range.upperBound, range.lowerBound + 1)),
                   onEditingChanged: { editing in if !editing { onCommit() } })
                .accessibilityIdentifier("\(id).slider")
            Stepper("", value: value, in: range, onEditingChanged: { editing in if !editing { onCommit() } })
                .labelsHidden()
                .accessibilityIdentifier("\(id).stepper")
            Button { snap(value) } label: { Image(systemName: "key") }
                .help("Snap to the nearest keyframe")
                .buttonStyle(.borderless)
                .accessibilityIdentifier("\(id).snap")
            Text("\(value.wrappedValue)").monospacedDigit().frame(width: 52, alignment: .trailing)
                .accessibilityIdentifier("\(id).value")
        }
    }

    private func snap(_ value: Binding<Int>) {
        let ks = clip.probe.keyframes + [clip.probe.frameCount]
        if let k = ks.min(by: { abs($0 - value.wrappedValue) < abs($1 - value.wrappedValue) }) {
            value.wrappedValue = k
            if clip.outFrame <= clip.inFrame { clip.outFrame = min(clip.inFrame + 1, clip.probe.frameCount) }
            onCommit()
        }
    }

    private func timecode(_ frames: Int) -> String {
        let s = Double(frames) / clip.probe.fps
        return String(format: "%d:%05.2f", Int(s) / 60, s.truncatingRemainder(dividingBy: 60))
    }
}

struct KeyframeStrip: View {
    let clip: Clip

    var body: some View {
        GeometryReader { geo in
            let n = CGFloat(max(clip.probe.frameCount, 1))
            let x = { (f: Int) in geo.size.width * CGFloat(f) / n }
            ZStack(alignment: .leading) {
                Rectangle().fill(.quaternary)
                Rectangle().fill(Color.accentColor.opacity(0.35))
                    .frame(width: max(1, x(clip.outFrame) - x(clip.inFrame)))
                    .offset(x: x(clip.inFrame))
                ForEach(clip.probe.keyframes, id: \.self) { k in
                    Rectangle().fill(.primary.opacity(0.6)).frame(width: 1).offset(x: x(k))
                }
            }
        }
        .help("Shaded: kept range. Ticks: keyframes (cuts there are free).")
    }
}
