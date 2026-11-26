import TetraStereo.Examples.FigureEightArmPriority

open TetraStereo.Examples.FigureEightArmOrbits TetraStereo.Examples.FigureEightArmPriority

def main : IO Unit := do
  for p in [false,true] do
    for c in [false,true] do
      for d in [false,true] do
        for e in [false,true] do
          IO.println s!"branch {p.toNat} {c.toNat} {d.toNat} {e.toNat} {(branchCode (p,c,d,e)).val}"
  for (a,b) in types do
    IO.println s!"arm {a.val} {b.val} {priority a b}"
