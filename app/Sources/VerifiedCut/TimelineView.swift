import AppKit
import SwiftUI

/// Where things sit on the shared time axis. A clip's whole source is drawn, placed so its
/// kept range lands at the clip's output start; the trimmed head and tail stick out either side.
struct TimelineLayout {
    static let pad: CGFloat = 16

    /// Output time of each clip's source frame 0.
    let origins: [Double]
    /// Leftmost and rightmost times drawn: trimmed heads can reach before 0.
    let t0: Double
    let tEnd: Double
    let pps: Double

    init(clips: [Clip], starts: [Double], frozen: [Clip.ID: Double]?, pps: Double) {
        origins = zip(clips, starts).map { c, s in frozen?[c.id] ?? s - c.seconds(c.inFrame) }
        t0 = min(0, origins.min() ?? 0)
        let ends = zip(clips, origins).map { c, o in o + c.seconds(c.probe.frameCount) }
        tEnd = max(starts.last.map { $0 + (clips.last.map { $0.seconds($0.length) } ?? 0) } ?? 0, ends.max() ?? 0)
        self.pps = pps
    }

    func x(_ t: Double) -> CGFloat { Self.pad + CGFloat((t - t0) * pps) }
    func t(_ x: CGFloat) -> Double { Double(x - Self.pad) / pps + t0 }
    var width: CGFloat { x(tEnd) + Self.pad }
}

func timecode(_ s: Double, fine: Bool = true) -> String {
    let s = max(0, s)
    return fine ? String(format: "%d:%05.2f", Int(s) / 60, s.truncatingRemainder(dividingBy: 60))
                : String(format: "%d:%02d", Int(s) / 60, Int(s) % 60)
}

private let laneColors: [Color] = [.blue, .teal, .purple, .orange, .pink, .green, .indigo, .mint]

struct TimelineEditor: View {
    @Bindable var timeline: Timeline
    /// Zoom, in points per second.
    @State private var pps: Double = 40
    @State private var pinchBase: Double?
    @State private var visibleWidth: CGFloat = 600
    /// Clip origins frozen for the length of a trim drag, so the dragged edge follows the cursor;
    /// later clips ripple when the drag ends.
    @State private var frozen: [Clip.ID: Double]?

    static let laneHeight: CGFloat = 70
    static let rulerHeight: CGFloat = 28
    static let headerWidth: CGFloat = 250
    static let ppsRange = 0.5...800.0

    var body: some View {
        let layout = TimelineLayout(clips: timeline.clips, starts: timeline.starts, frozen: frozen, pps: pps)
        ScrollView(.vertical) {
            HStack(alignment: .top, spacing: 0) {
                VStack(spacing: 0) {
                    zoomControls.frame(height: Self.rulerHeight)
                    ForEach(Array($timeline.clips.enumerated()), id: \.element.id) { i, $clip in
                        LaneHeader(clip: $clip, index: i, count: timeline.clips.count, color: laneColors[clip.tint % laneColors.count],
                                   onCommit: { Task { await timeline.refresh() } },
                                   onShift: { d in Task { await timeline.shift(clip.id, by: d) } },
                                   onRemove: { Task { await timeline.remove(clip) } })
                            .frame(height: Self.laneHeight)
                    }
                }
                .frame(width: Self.headerWidth)
                .background(Color(white: 0.13))
                Divider()
                ScrollView(.horizontal) {
                    VStack(spacing: 0) {
                            Ruler(layout: layout, duration: timeline.duration)
                                .frame(height: Self.rulerHeight)
                                .contentShape(Rectangle())
                                .gesture(DragGesture(minimumDistance: 0, coordinateSpace: .named("timeline"))
                                    .onChanged { timeline.seek(to: layout.t($0.location.x)) })
                                .accessibilityElement()
                                .accessibilityIdentifier("timeline.ruler")
                                .accessibilityLabel("Ruler")
                            ForEach(Array($timeline.clips.enumerated()), id: \.element.id) { i, $clip in
                                ClipLane(clip: $clip, start: timeline.starts[i], origin: layout.origins[i], layout: layout,
                                         color: laneColors[clip.tint % laneColors.count],
                                         onBegin: { frozen = Dictionary(uniqueKeysWithValues: zip(timeline.clips.map(\.id), layout.origins)) },
                                         onEnd: { frozen = nil; Task { await timeline.refresh() } },
                                         onSeek: { timeline.seek(to: $0) })
                                    .frame(height: Self.laneHeight)
                                    .background(i % 2 == 0 ? Color(white: 0.15) : Color(white: 0.165))
                            }
                    }
                    .overlay(alignment: .topLeading) { Playhead(timeline: timeline, layout: layout) }
                    .frame(width: max(layout.width, visibleWidth), alignment: .leading)
                    .coordinateSpace(name: "timeline")
                }
                .background(GeometryReader { g in
                    Color.clear.onAppear { visibleWidth = g.size.width }
                        .onChange(of: g.size.width) { visibleWidth = $1 }
                })
            }
            .overlay(alignment: .center) {
                if timeline.clips.isEmpty {
                    Text("Drop clips here, or Import…").foregroundStyle(.secondary).padding(.top, 40)
                }
            }
        }
        .background(Color(white: 0.11))
        .simultaneousGesture(MagnifyGesture()
            .onChanged { v in
                let base = pinchBase ?? pps
                pinchBase = base
                pps = clampZoom(base * v.magnification)
            }
            .onEnded { _ in pinchBase = nil })
        .dropDestination(for: URL.self) { urls, _ in
            Task { await timeline.add(urls) }
            return true
        }
        .onChange(of: timeline.clips.count) { old, new in
            if new > old { fit(TimelineLayout(clips: timeline.clips, starts: timeline.starts, frozen: nil, pps: pps)) }
        }
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("clip.list")
    }

    private var zoomControls: some View {
        HStack(spacing: 6) {
            Image(systemName: "minus.magnifyingglass").foregroundStyle(.secondary)
            Slider(value: Binding(get: { log(pps) }, set: { pps = clampZoom(exp($0)) }),
                   in: log(Self.ppsRange.lowerBound)...log(Self.ppsRange.upperBound))
                .controlSize(.mini)
                .accessibilityIdentifier("timeline.zoom")
            Image(systemName: "plus.magnifyingglass").foregroundStyle(.secondary)
            Button("Fit") { fit(TimelineLayout(clips: timeline.clips, starts: timeline.starts, frozen: nil, pps: pps)) }
                .controlSize(.small)
                .accessibilityIdentifier("timeline.fit")
        }
        .padding(.horizontal, 10)
    }

    private func clampZoom(_ v: Double) -> Double { min(max(v, Self.ppsRange.lowerBound), Self.ppsRange.upperBound) }

    /// Zoom so the whole timeline, trimmed parts included, fills the visible width.
    private func fit(_ layout: TimelineLayout) {
        let span = layout.tEnd - layout.t0
        guard span > 0 else { return }
        pps = clampZoom(Double(visibleWidth - 2 * TimelineLayout.pad) / span)
    }
}

/// Fixed-width column left of each lane: name, exact In/Out frames, order and removal.
struct LaneHeader: View {
    @Binding var clip: Clip
    let index: Int
    let count: Int
    let color: Color
    var onCommit: () -> Void
    var onShift: (Int) -> Void
    var onRemove: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            HStack(spacing: 6) {
                RoundedRectangle(cornerRadius: 2).fill(color).frame(width: 4, height: 14)
                Text(clip.name).font(.callout.weight(.medium)).lineLimit(1).truncationMode(.middle)
                    .help(clip.url.path)
                    .accessibilityIdentifier("clip.name")
                Spacer(minLength: 0)
                Button { onShift(-1) } label: { Image(systemName: "chevron.up") }
                    .disabled(index == 0).help("Move earlier")
                    .accessibilityIdentifier("clip.up")
                Button { onShift(1) } label: { Image(systemName: "chevron.down") }
                    .disabled(index == count - 1).help("Move later")
                    .accessibilityIdentifier("clip.down")
                Button(role: .destructive, action: onRemove) { Image(systemName: "trash") }
                    .help("Remove clip")
                    .accessibilityIdentifier("clip.remove")
            }
            .buttonStyle(.borderless)
            Text("\(clip.length) frames · \(timecode(clip.seconds(clip.length)))")
                .font(.caption).foregroundStyle(.secondary).monospacedDigit()
                .accessibilityIdentifier("clip.length")
            HStack(spacing: 10) {
                frameControl("In", id: "clip.in", value: $clip.inFrame, range: 0...(clip.outFrame - 1))
                frameControl("Out", id: "clip.out", value: $clip.outFrame, range: (clip.inFrame + 1)...clip.probe.frameCount)
            }
            .font(.caption)
        }
        .padding(.horizontal, 10)
        .frame(maxHeight: .infinity)
        .overlay(alignment: .bottom) { Divider() }
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("clip.row")
    }

    private func frameControl(_ label: String, id: String, value: Binding<Int>, range: ClosedRange<Int>) -> some View {
        HStack(spacing: 2) {
            Text(label).foregroundStyle(.secondary)
            Text("\(value.wrappedValue)").monospacedDigit().frame(minWidth: 34, alignment: .trailing)
                .accessibilityIdentifier("\(id).value")
            Stepper("", value: value, in: range, onEditingChanged: { editing in if !editing { onCommit() } })
                .labelsHidden().controlSize(.mini)
                .accessibilityIdentifier("\(id).stepper")
            Button { snap(value) } label: { Image(systemName: "key") }
                .buttonStyle(.borderless)
                .help("Snap to the nearest keyframe")
                .accessibilityIdentifier("\(id).snap")
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
}

/// One clip's whole source as a rectangle on the time axis; the kept range is bright,
/// the trimmed head and tail faded. Its edges are the trim handles.
struct ClipLane: View {
    @Binding var clip: Clip
    let start: Double
    let origin: Double
    let layout: TimelineLayout
    let color: Color
    var onBegin: () -> Void
    var onEnd: () -> Void
    var onSeek: (Double) -> Void

    @State private var dragFrom: Int?
    private let thumbs = Thumbnails.shared
    static let handleWidth: CGFloat = 9
    /// Within this distance a dragged edge sticks to a keyframe, where the cut is free.
    static let snapDistance: CGFloat = 6

    var body: some View {
        let pps = layout.pps
        let full = CGFloat(clip.seconds(clip.probe.frameCount) * pps)
        let head = CGFloat(clip.seconds(clip.inFrame) * pps)
        let kept = max(CGFloat(clip.seconds(clip.length) * pps), 2)
        ZStack(alignment: .topLeading) {
            Filmstrip(images: thumbs.strips[clip.url], color: color)
                .frame(width: full)
            Rectangle().fill(.black.opacity(0.62)).frame(width: head)
            Rectangle().fill(.black.opacity(0.62)).frame(width: max(0, full - head - kept)).offset(x: head + kept)
            KeyframeTicks(clip: clip)
                .frame(width: full, height: 7)
                .offset(y: TimelineEditor.laneHeight - 15)
                .accessibilityElement()
                .accessibilityIdentifier("clip.keyframes")
                .accessibilityLabel("Keyframes")
            keptRegion(width: kept).offset(x: head)
            handle(.in).offset(x: head)
            handle(.out).offset(x: head + kept - Self.handleWidth)
        }
        .frame(width: full, height: TimelineEditor.laneHeight - 10, alignment: .topLeading)
        .clipShape(RoundedRectangle(cornerRadius: 5))
        .offset(x: layout.x(origin), y: 5)
        .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)
        .onAppear { thumbs.request(clip.url, duration: clip.seconds(clip.probe.frameCount)) }
        .accessibilityElement(children: .contain)
        .accessibilityIdentifier("clip.lane")
    }

    private func keptRegion(width: CGFloat) -> some View {
        RoundedRectangle(cornerRadius: 5)
            .strokeBorder(color, lineWidth: 2)
            .background(alignment: .topLeading) {
                Text(clip.name).font(.caption2.weight(.semibold)).lineLimit(1)
                    .padding(.horizontal, 5).padding(.vertical, 2)
                    .background(.black.opacity(0.55), in: RoundedRectangle(cornerRadius: 3))
                    .padding(.leading, Self.handleWidth + 2).padding(.top, 3)
                    .frame(width: width, alignment: .leading).clipped()
            }
            .frame(width: width)
            .contentShape(Rectangle())
            .gesture(SpatialTapGesture(coordinateSpace: .named("timeline")).onEnded { v in
                onSeek(min(max(layout.t(v.location.x), start), start + clip.seconds(clip.length)))
            })
    }

    private enum Edge { case `in`, out }

    private func handle(_ edge: Edge) -> some View {
        let id = edge == .in ? "clip.in.handle" : "clip.out.handle"
        return UnevenRoundedRectangle(cornerRadii: edge == .in ? .init(topLeading: 5, bottomLeading: 5)
                                                               : .init(bottomTrailing: 5, topTrailing: 5))
            .fill(color)
            .overlay { Capsule().fill(.white.opacity(0.8)).frame(width: 2, height: 16) }
            .frame(width: Self.handleWidth)
            .contentShape(Rectangle())
            .onHover { inside in if inside { NSCursor.resizeLeftRight.push() } else { NSCursor.pop() } }
            .gesture(DragGesture(minimumDistance: 1, coordinateSpace: .named("timeline"))
                .onChanged { v in drag(edge, by: v.translation.width) }
                .onEnded { _ in dragFrom = nil; onEnd() })
            .help(edge == .in ? "Drag to trim the start" : "Drag to trim the end")
            .accessibilityElement()
            .accessibilityIdentifier(id)
            .accessibilityLabel(edge == .in ? "In point" : "Out point")
            .accessibilityValue("\(edge == .in ? clip.inFrame : clip.outFrame)")
            .accessibilityAdjustableAction { dir in
                let d = dir == .increment ? 1 : dir == .decrement ? -1 : 0
                set(edge, edge == .in ? clip.inFrame + d : clip.outFrame + d)
                onEnd()
            }
    }

    private func drag(_ edge: Edge, by dx: CGFloat) {
        if dragFrom == nil {
            dragFrom = edge == .in ? clip.inFrame : clip.outFrame
            onBegin()
        }
        guard let from = dragFrom else { return }
        var f = clip.frame(at: clip.seconds(from) + Double(dx) / layout.pps)
        let ks = clip.probe.keyframes + [clip.probe.frameCount]
        if let k = ks.min(by: { abs($0 - f) < abs($1 - f) }),
           CGFloat(abs(clip.seconds(k - f)) * layout.pps) <= Self.snapDistance {
            f = k
        }
        set(edge, f)
    }

    private func set(_ edge: Edge, _ f: Int) {
        switch edge {
        case .in: clip.inFrame = min(max(f, 0), clip.outFrame - 1)
        case .out: clip.outFrame = min(max(f, clip.inFrame + 1), clip.probe.frameCount)
        }
    }
}

struct Filmstrip: View {
    let images: [CGImage?]?
    let color: Color

    var body: some View {
        GeometryReader { g in
            let n = images?.count ?? 1
            let w = g.size.width / CGFloat(n)
            ZStack(alignment: .leading) {
                LinearGradient(colors: [color.opacity(0.55), color.opacity(0.3)], startPoint: .top, endPoint: .bottom)
                if let images {
                    // Tiles narrower than this would just be noise, so draw fewer, wider ones.
                    let stride = max(1, Int((28 / w).rounded(.up)))
                    ForEach(Array(Swift.stride(from: 0, to: n, by: stride)), id: \.self) { i in
                        if let img = images[i] {
                            Image(decorative: img, scale: 1)
                                .resizable().aspectRatio(contentMode: .fill)
                                .frame(width: w * CGFloat(min(stride, n - i)), height: g.size.height)
                                .clipped()
                                .offset(x: w * CGFloat(i))
                        }
                    }
                }
            }
        }
    }
}

struct KeyframeTicks: View {
    let clip: Clip

    var body: some View {
        Canvas { ctx, size in
            let n = CGFloat(max(clip.probe.frameCount, 1))
            for k in clip.probe.keyframes {
                ctx.fill(Path(CGRect(x: size.width * CGFloat(k) / n, y: 0, width: 1, height: size.height)),
                         with: .color(.white.opacity(0.7)))
            }
        }
        .help("Ticks: keyframes (cuts there are free)")
        .allowsHitTesting(false)
    }
}

struct Ruler: View {
    let layout: TimelineLayout
    let duration: Double

    var body: some View {
        Canvas { ctx, size in
            ctx.fill(Path(CGRect(origin: .zero, size: size)), with: .color(Color(white: 0.18)))
            // Outside the output (trimmed heads before 0, tails after the end): darker.
            ctx.fill(Path(CGRect(x: 0, y: 0, width: layout.x(0), height: size.height)), with: .color(.black.opacity(0.3)))
            ctx.fill(Path(CGRect(x: layout.x(duration), y: 0, width: max(0, size.width - layout.x(duration)), height: size.height)),
                     with: .color(.black.opacity(0.3)))
            let steps = [0.1, 0.2, 0.5, 1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 1800, 3600]
            let step = steps.first { $0 * layout.pps >= 80 } ?? 3600
            let minor = step / (step == 15 || step == 30 ? 3 : 5)
            var t = (layout.t0 / minor).rounded(.down) * minor
            while t <= layout.t(size.width) {
                let x = layout.x(t)
                let major = abs((t / step).rounded() * step - t) < minor / 2
                ctx.fill(Path(CGRect(x: x, y: size.height - (major ? 10 : 5), width: 1, height: major ? 10 : 5)),
                         with: .color(.white.opacity(major ? 0.6 : 0.3)))
                if major && t >= -1e-9 && x + 40 < size.width {
                    ctx.draw(Text(timecode(t, fine: step < 1)).font(.caption2.monospacedDigit()).foregroundStyle(.secondary),
                             at: CGPoint(x: x + 3, y: 2), anchor: .topLeading)
                }
                t += minor
            }
            ctx.fill(Path(CGRect(x: 0, y: size.height - 1, width: size.width, height: 1)), with: .color(.black.opacity(0.5)))
        }
    }
}

/// Reads the player time on its own, so only this view redraws while playing.
struct Playhead: View {
    let timeline: Timeline
    let layout: TimelineLayout

    var body: some View {
        let x = layout.x(timeline.playhead)
        ZStack(alignment: .top) {
            Rectangle().fill(Color.red).frame(width: 1.5)
            Path { p in
                p.move(to: CGPoint(x: -6, y: 0)); p.addLine(to: CGPoint(x: 6, y: 0)); p.addLine(to: CGPoint(x: 0, y: 9))
                p.closeSubpath()
            }
            .fill(Color.red)
            .frame(width: 0, height: 9)
        }
        .frame(width: 1.5)
        .frame(maxHeight: .infinity)
        .offset(x: x - 0.75)
        .allowsHitTesting(false)
        .accessibilityElement()
        .accessibilityIdentifier("timeline.playhead")
        .accessibilityValue(timecode(timeline.playhead))
    }
}
