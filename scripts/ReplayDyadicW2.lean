import DyadicEnergyReplay

open YangMills.DyadicExp YangMills.DyadicPartition YangMills.DyadicEnergyReplay

def main : IO Unit := do
  let cells := cache angleCell
  for b in ([1000,1272,1500,1800,1900,1950,2000,2200,2400,2450,2500,2600,2750,2800,2830,2880] : List Int) do
    for k in [:128] do
      let rl := fieldLo b k
      let rh := fieldHi b k
      let (p,s) := evaluate cells rl rh
      IO.println s!"{b} {k} {p} {s}"
