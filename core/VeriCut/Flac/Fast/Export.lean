import VeriCut.Export
import VeriCut.Flac.Fast.Encode

namespace VeriCut

/-- `exportClips` with the fast encoder: what `vericut export` runs. -/
def exportClipsFast (st : Flac.Fast.Settings) (format : Format) (clips : List Clip) : ByteArray :=
  Flac.Fast.encodeFast st (splice format clips)

end VeriCut
