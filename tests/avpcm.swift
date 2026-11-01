// Decode a file's first audio track with AVFoundation (edit lists applied) to s16le mono on stdout.
import AVFoundation
let url = URL(fileURLWithPath: CommandLine.arguments[1])
let asset = AVURLAsset(url: url)
let sem = DispatchSemaphore(value: 0)
var tracks: [AVAssetTrack] = []
Task { tracks = try await asset.loadTracks(withMediaType: .audio); sem.signal() }
sem.wait()
let reader = try AVAssetReader(asset: asset)
let out = AVAssetReaderTrackOutput(track: tracks[0], outputSettings: [
  AVFormatIDKey: kAudioFormatLinearPCM, AVLinearPCMBitDepthKey: 16, AVLinearPCMIsFloatKey: false,
  AVLinearPCMIsBigEndianKey: false, AVLinearPCMIsNonInterleaved: false, AVNumberOfChannelsKey: 1])
reader.add(out)
reader.startReading()
var data = Data()
while let sb = out.copyNextSampleBuffer(), let bb = CMSampleBufferGetDataBuffer(sb) {
  var len = 0; var ptr: UnsafeMutablePointer<Int8>?
  CMBlockBufferGetDataPointer(bb, atOffset: 0, lengthAtOffsetOut: nil, totalLengthOut: &len, dataPointerOut: &ptr)
  data.append(UnsafeBufferPointer(start: ptr, count: len))
}
if reader.status != .completed { FileHandle.standardError.write("reader: \(String(describing: reader.error))\n".data(using: .utf8)!); exit(1) }
FileHandle.standardOutput.write(data)
