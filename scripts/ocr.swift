// Print the text Vision recognises in an image, one line per observation, top to bottom.
// Usage: swift scripts/ocr.swift shot.png
import AppKit
import Vision

let url = URL(fileURLWithPath: CommandLine.arguments[1])
guard let img = NSImage(contentsOf: url),
      let cg = img.cgImage(forProposedRect: nil, context: nil, hints: nil) else {
    fatalError("cannot read \(url.path)")
}
let req = VNRecognizeTextRequest()
req.recognitionLevel = .accurate
try VNImageRequestHandler(cgImage: cg).perform([req])
for o in (req.results ?? []).sorted(by: { $0.boundingBox.minY > $1.boundingBox.minY }) {
    if let t = o.topCandidates(1).first { print(t.string) }
}
