import DyadicTrig

open YangMills.DyadicTrig

def main : IO Unit := do
  for i in [:2048] do
    let sq := sinSqBounds i
    IO.println s!"{i} {(cosBounds 11 (i+1)).1} {(cosBounds 11 i).2} {sq.1} {sq.2}"
