import DyadicTrig
import DyadicExp

open YangMills.DyadicTrig YangMills.DyadicExp

structure Cell where
  cosLo : Int
  cosHi : Int
  sinLo : Int
  sinHi : Int
  deriving Inhabited

def angles : Array Cell := (Array.range 2048).map fun i =>
  let sq := sinSqBounds i
  ⟨(cosBounds 11 (i+1)).1 / 4, ceilDiv (cosBounds 11 i).2 4,
    sq.1 / 4194304, ceilDiv sq.2 4194304⟩

def loMul (x lo hi : Int) := min (x*lo) (x*hi) / q
def hiMul (x lo hi : Int) := ceilDiv (max (x*lo) (x*hi)) q

/-- Independently evaluate the cell sums with arbitrary-precision signed integers. -/
def fieldEnergies (cells : Array Cell) (rl rh : Int) : Int × Int := Id.run do
  let mut weights : Array (Int × Int) := #[]
  let mut zl := 0
  let mut zh := 0
  let mut ml := 0
  let mut mh := 0
  let mut transverse := 0
  for c in cells do
    let xl := loMul c.cosLo rl rh
    let xh := hiMul c.cosHi rl rh
    let wl := c.sinLo * expLo xl / q
    let wh := ceilDiv (c.sinHi * expHi xh) q
    weights := weights.push (wl,wh)
    zl := zl + wl
    zh := zh + wh
    ml := ml + loMul c.cosLo wl wh
    mh := mh + hiMul c.cosHi wl wh
    let d := max (-((2*q-hiMul xh c.sinLo c.sinHi)/6)) (ceilDiv (2*q-loMul xl c.sinLo c.sinHi) 6)
    let a := max (-c.cosLo) c.cosHi
    let cost := ceilDiv (ceilDiv (a*a) q) 27 + ceilDiv (2*ceilDiv (d*d) q) 3
    transverse := transverse + ceilDiv (cost*wh) q
  zl := zl/2048
  zh := ceilDiv zh 2048
  ml := ml/2048*q
  mh := ceilDiv mh 2048*q
  ml := min (ml/zl) (ml/zh)
  mh := max (ceilDiv mh zl) (ceilDiv mh zh)
  let mut energy := 0
  for side in [:2] do
    let mut fl := 0
    let mut fh := 0
    for j in [:1024] do
      let i := if side == 0 then j else 2047-j
      let (wl,wh) := weights[i]!
      let c := cells[i]!
      let cl := if side == 0 then c.cosLo-mh else ml-c.cosHi
      let ch := if side == 0 then c.cosHi-ml else mh-c.cosLo
      let dl := loMul cl wl wh
      let dh := hiMul ch wl wh
      let f := ceilDiv (max (-(fl+min 0 dl)) (fh+max 0 dh)) 2048
      energy := energy + (if j == 0 then ceilDiv (16*wh) 4194304 else ceilDiv (f*f) wl)
      fl := fl+dl
      fh := fh+dh
  let parallel := ceilDiv (ceilDiv (ceilDiv energy 2048*q) zl * 986961) 100000
  return (parallel, ceilDiv (ceilDiv transverse 2048*q) zl)

def main : IO Unit := do
  let cells := angles
  for b in ([1000,1272,1500,1800,1900,1950,2000,2200,2400,2450,2500,2600,2750,2800,2830,2880] : List Int) do
    for k in [:128] do
      let rl := 6*b*q*k/1280000
      let rh := ceilDiv (6*b*q*(k+1)) 1280000
      let (p,s) := fieldEnergies cells rl rh
      IO.println s!"{b} {k} {p} {s}"
