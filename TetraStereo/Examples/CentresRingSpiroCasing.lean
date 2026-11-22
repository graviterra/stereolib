import TetraStereo.Engine.CentresRingMirror

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace TetraStereo.Examples.CentresRingSpiroCasing
open OneCenter Engine Engine.CentresRing

/-- Two cyclopropane rings meet at carbon 0. Each of carbons 1 through 4
has one fluorine and one hydrogen. Atom numbers start at zero. -/
def molecule : RawMolecule where
  atoms := List.replicate 5 (.aliphatic .C) ++ List.replicate 4 (.aliphatic .F) ++
    List.replicate 4 (.aliphatic .H)
  bonds := ([(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(1,5),(1,9),(2,6),(2,10),
    (3,7),(3,11),(4,8),(4,12)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

/-- Constructed rational coordinates. The two rings are in perpendicular planes. -/
def spatial : SpatialConfiguration := ⟨[⟨0,0,0⟩, ⟨2,1,0⟩, ⟨2,-1,0⟩, ⟨-2,0,1⟩, ⟨-2,0,-1⟩, ⟨3,2,1⟩, ⟨3,-2,1⟩, ⟨-3,1,2⟩, ⟨-3,1,-2⟩, ⟨3,2,-1⟩, ⟨3,-2,-1⟩, ⟨-3,-1,2⟩, ⟨-3,-1,-2⟩]⟩

/-- An involution on the existing indices. It changes the numbers of two carbons. -/
def rename (i : Nat) := if i = 0 then 3 else if i = 3 then 0 else i

def renumbered : RawMolecule := {molecule with
  bonds := molecule.bonds.map fun b => {b with source := rename b.source, target := rename b.target}}

def moved : SpatialConfiguration := ⟨(List.range 13).filterMap fun i => spatial.positions[rename i]?⟩
def reflected (g : SpatialConfiguration) : SpatialConfiguration := MirrorCasing.reflectGeometry g

/-- Both graph presentations carry exactly the same atom specifications,
bond orders and positions under the involution. -/
theorem same_molecule :
    (∀ i : Fin 13, rename (rename i) = i ∧
      renumbered.atoms[rename i]? = molecule.atoms[i.val]? ∧
      moved.positions[rename i]? = spatial.positions[i.val]?) ∧
    ∀ i j : Fin 13, renumbered.bondOrder (rename i) (rename j) = molecule.bondOrder i j := by
  decide +kernel

/-- Initial edge orders and path discovery from the pinned source. The two
mirror runs have the same layouts as their respective original runs. No
comparison value, auxiliary label or reported result enters a layout. -/
def originalLayouts : List Molecular.Layout := [
  ⟨0, [[1, 0], [1, 2, 0], [2, 0], [2, 1, 0], [3, 0], [3, 4, 0], [4, 0], [4, 3, 0]], [[1, 2, 3, 4], [4, 3, 2, 1]], [[2, 5, 0, 9], [1, 6, 0, 10], [4, 7, 0, 11], [3, 8, 0, 12], [2, 5, 0, 9], [1, 6, 0, 10], [4, 7, 0, 11], [3, 8, 0, 12]]⟩,
  ⟨1, [], [[0, 2, 5, 9]], []⟩,
  ⟨2, [], [[0, 1, 6, 10]], []⟩,
  ⟨3, [], [[0, 4, 7, 11]], []⟩,
  ⟨4, [], [[0, 3, 8, 12]], []⟩]

def renumberedLayouts : List Molecular.Layout := [
  ⟨0, [], [[3, 4, 7, 11]], []⟩,
  ⟨1, [], [[3, 2, 5, 9]], []⟩,
  ⟨2, [], [[3, 1, 6, 10]], []⟩,
  ⟨3, [[0, 3], [0, 4, 3], [1, 3], [1, 2, 3], [2, 3], [2, 1, 3], [4, 3], [4, 0, 3]], [[1, 2, 0, 4], [4, 2, 1, 0]], [[4, 7, 3, 11], [2, 5, 3, 9], [1, 6, 3, 10], [0, 8, 3, 12], [4, 7, 3, 11], [2, 5, 3, 9], [1, 6, 3, 10], [0, 8, 3, 12]]⟩,
  ⟨4, [], [[3, 0, 8, 12]], []⟩]

/-- Recompute every auxiliary from the empty store before reading the recorded
center. The deciding order and the number of doubled comparisons are exposed. -/
def outcome (m : RawMolecule) (g : SpatialConfiguration) (l : Molecular.Layout) :
    Option (String × List Nat × Nat) := do
  let d ← Molecular.derive m (fun i => g.positions[i]?) l
  let last ← d.trace.passes.getLast?
  let trial ← last.trials.getLast?
  let r ← (replaySort trial).toOption
  guard r.unique
  return (d.trace.label,r.order,r.pseudoCount)

def center (m : RawMolecule) (g : SpatialConfiguration) (layouts : List Molecular.Layout)
    (i : Nat) := (layouts.find? (fun l => l.root == i)).bind (outcome m g)

def fullReport (m : RawMolecule) (g : SpatialConfiguration) (layouts : List Molecular.Layout) :=
  layouts.mapM fun l => do
    let d ← Molecular.derive m (fun i => g.positions[i]?) l
    return (d.trace.atom,d.trace.label)

/-- All five centers in the ordinary and mirror reports, with their complete configured inventory. -/
theorem original_outcome :
    center molecule spatial originalLayouts 0 = some ("S",[1, 3, 2, 4],2) := by decide +kernel

theorem original_report :
    fullReport molecule spatial originalLayouts =
      some [(0,"S"), (1,"R"), (2,"S"), (3,"R"), (4,"S")] := by decide +kernel

theorem renumbered_outcome :
    center renumbered moved renumberedLayouts 3 = some ("s",[0, 1, 4, 2],1) := by decide +kernel

theorem renumbered_report :
    fullReport renumbered moved renumberedLayouts =
      some [(0,"R"), (1,"R"), (2,"S"), (3,"s"), (4,"S")] := by decide +kernel

theorem original_mirror_outcome :
    center molecule (reflected spatial) originalLayouts 0 = some ("R",[2, 4, 1, 3],2) := by decide +kernel

theorem original_mirror_report :
    fullReport molecule (reflected spatial) originalLayouts =
      some [(0,"R"), (1,"S"), (2,"R"), (3,"S"), (4,"R")] := by decide +kernel

theorem renumbered_mirror_outcome :
    center renumbered (reflected moved) renumberedLayouts 3 = some ("r",[2, 4, 1, 0],1) := by decide +kernel

theorem renumbered_mirror_report :
    fullReport renumbered (reflected moved) renumberedLayouts =
      some [(0,"S"), (1,"S"), (2,"R"), (3,"r"), (4,"R")] := by decide +kernel

/-- Structural admission succeeds in all four presentations. -/
theorem admitted :
    (LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome = true ∧
    (LocalizedChemicalRing.admitRawSpatial? molecule (reflected spatial)).isSome = true ∧
    (LocalizedChemicalRing.admitRawSpatial? renumbered moved).isSome = true ∧
    (LocalizedChemicalRing.admitRawSpatial? renumbered (reflected moved)).isSome = true := by
  decide +kernel

open LocalizedGenericMarkedRecalculation (readback? caseFromMirror? mirror)

/-- For either independent choice in each geometry, following the two ring
partnerships yields S in both numberings. This calculation uses the coordinates
and the specified pairs, independently of the historical sort count. -/
theorem linked_spiro_casing (x y : Bool) :
    caseFromMirror? (readback? (fun i => spatial.positions[i]?) (MirrorCasing.linkedOrder x 1 3 2 4))
      (readback? (mirror (fun i => spatial.positions[i]?)) (MirrorCasing.linkedOrder y 2 4 1 3)) =
        some (.chiral .S) ∧
    caseFromMirror? (readback? (fun i => moved.positions[i]?) (MirrorCasing.linkedOrder x 0 1 4 2))
      (readback? (mirror (fun i => moved.positions[i]?)) (MirrorCasing.linkedOrder y 4 2 0 1)) =
        some (.chiral .S) := by
  simp only [MirrorCasing.linked_pairs_uppercase]
  decide +kernel

/-- Constitutional order at a fluorinated peripheral carbon of this scaffold.
Among its two carbon neighbors, the other peripheral carbon presents F,C,H
and the spiro atom presents C,C,C. -/
private def peripheralHand (m : RawMolecule) (g : SpatialConfiguration) (root atom : Nat) :
    Option RS := do
  let ns := m.writtenNeighbors atom
  let elem (n : Nat) := (m.atoms[n]?).map (fun a => a.element.atomicNumber)
  let [f] := ns.filter (fun n => elem n == some 9) | none
  let [h] := ns.filter (fun n => elem n == some 1) | none
  let [peer] := ns.filter (fun n => n != root && elem n == some 6) | none
  guard (ns.length == 4 && ns.contains root && elem root == some 6)
  readback? (fun i => g.positions[i]?) [f,peer,root,h]

/-- Examine all 24 orders of the spiro ligands. The R branches are senior to
the S branches. Selecting the first ligand selects its ring partner for third
place. This test reads the molecular graph and coordinates alone. -/
def scaffoldOrders (m : RawMolecule) (g : SpatialConfiguration) (root : Nat) : List (List Nat) :=
  (m.writtenNeighbors root).permutations'.filter fun
    | [a,b,c,d] => [a,b,c,d].map (peripheralHand m g root) == [some .R,some .R,some .S,some .S] &&
        m.bondOrder a c == 1 && m.bondOrder b d == 1
    | _ => false

def allScaffoldOrdersRead (m : RawMolecule) (g : SpatialConfiguration) (root : Nat) (h : RS) : Bool :=
  let orders := scaffoldOrders m g root
  orders.length == 2 && orders.all (fun order => readback? (fun i => g.positions[i]?) order == some h)

/-- In each presentation precisely two orders satisfy the independent scaffold
test. All their readbacks agree. Reflection reverses every one. -/
theorem independent_scaffold_readings :
    allScaffoldOrdersRead molecule spatial 0 .S = true ∧ allScaffoldOrdersRead molecule (reflected spatial) 0 .R = true ∧
    allScaffoldOrdersRead renumbered moved 3 .S = true ∧ allScaffoldOrdersRead renumbered (reflected moved) 3 .R = true := by
  decide +kernel

/-- All four decisive source priority orders pass the independent scaffold test.
The renumbered source discrepancy occurs even with these orders. -/
theorem actual_orders_follow_rings :
    [1,3,2,4] ∈ scaffoldOrders molecule spatial 0 ∧
    [2,4,1,3] ∈ scaffoldOrders molecule (reflected spatial) 0 ∧
    [0,1,4,2] ∈ scaffoldOrders renumbered moved 3 ∧
    [2,4,1,0] ∈ scaffoldOrders renumbered (reflected moved) 3 := by decide +kernel

/-- No descriptor and its chemical reflection reproduce the two renumbered runs. -/
theorem no_mirror_fidelity :
    ¬ ∃ d : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel,
      some (labelCode (some d)) = (center renumbered moved renumberedLayouts 3).map Prod.fst ∧
      some (labelCode (some (MirrorCasing.reflectLabel d))) =
        (center renumbered (reflected moved) renumberedLayouts 3).map Prod.fst := by
  rw [renumbered_outcome,renumbered_mirror_outcome]
  rintro ⟨(h | h),a,b⟩ <;> cases h <;> contradiction

/-- Any atom-number invariant chemical label would have to give the same
answer on these two presentations. Matching both complete source runs forbids it. -/
theorem no_invariant_fidelity :
    ¬ ∃ label : RawMolecule → SpatialConfiguration → Nat → Option String,
      label molecule spatial 0 = label renumbered moved (rename 0) ∧
      label molecule spatial 0 = (center molecule spatial originalLayouts 0).map Prod.fst ∧
      label renumbered moved (rename 0) =
        (center renumbered moved renumberedLayouts 3).map Prod.fst := by
  rintro ⟨_,same,left,right⟩
  rw [left,right,original_outcome,renumbered_outcome] at same
  contradiction

end TetraStereo.Examples.CentresRingSpiroCasing
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.same_molecule
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.no_invariant_fidelity
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.original_outcome
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.original_report
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.renumbered_outcome
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.renumbered_report
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.original_mirror_outcome
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.original_mirror_report
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.renumbered_mirror_outcome
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.renumbered_mirror_report
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.admitted
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.linked_spiro_casing
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.independent_scaffold_readings
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.actual_orders_follow_rings
assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.no_mirror_fidelity
