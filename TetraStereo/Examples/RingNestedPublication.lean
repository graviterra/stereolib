import TetraStereo.Engine.RingMolecularSchedule
import TetraStereo.Engine.CentresRing
import TetraStereo.Examples.RingPairedAuxiliary

set_option autoImplicit false
set_option maxRecDepth 35000
set_option maxHeartbeats 3500000
set_option Elab.async false

namespace TetraStereo.Examples.RingNestedPublication

open OneCenter Engine CertifiedLocalizedCIPInput
open RingNestedActivePair (Labels)
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission

/-- Ring carbon 1 has two constitutionally matching carbon substituents.
Atoms 17 and 21 are tetrahedral CH(F)Cl sites of opposite hand. Thus the
source actually enters its auxiliary pass when assigning this original root.
Carbon 0 retains the two constitutionally equal two-center arms. -/
def molecule : RawMolecule :=
  {RingPairedAuxiliary.molecule with
    atoms := RingPairedAuxiliary.molecule.atoms.set 1 (.aliphatic .C) ++
      ([.C,.F,.Cl,.H,.C,.F,.Cl,.H] : List Element).map AtomSpec.aliphatic
    bonds := RingPairedAuxiliary.molecule.bonds ++
      ([(1,17),(17,18),(17,19),(17,20),(1,21),(21,22),(21,23),(21,24)] : List (Nat × Nat)).map
        (fun (a,b) => ⟨a,b,.single⟩)}

private def params : List Nat := [0,1,2,3,4,5,6,8,7,9,10,11,12,13,15,14,16,17,18,19,20,21,23,22,24]
private def moment (t : ℚ) : CartesianPoint3 := ⟨t,t*t,t*t*t⟩
def spatial : SpatialConfiguration := ⟨params.map fun n => moment n⟩

def input := (LocalizedChemicalRing.admitRawSpatial? molecule spatial).get (by decide +kernel)

theorem admitted : LocalizedChemicalRing.admitRawSpatial? molecule spatial = some input :=
  (Option.some_get _).symm

private def param (a : input.certified.Atom) : Nat := params[a.val]?.getD 0

private theorem point (a : input.certified.Atom) :
    input.certified.spatialPointAt? a = some (moment (param a)) := by
  revert a
  decide +kernel

private theorem param_injective : Function.Injective param := by unfold Function.Injective; decide +kernel

private theorem volume (a b c d : ℚ) :
    CartesianPoint3.orientedVolume (moment a) (moment b) (moment c) (moment d) =
      (d-a)*(a-b)*(a-c)*(b-c)*(b-d)*(c-d) := by
  unfold moment CartesianPoint3.orientedVolume
  ring

theorem calibrated : LocalizedChemicalRing.coordinatesAdmitted input = true := by
  apply decide_eq_true
  intro center
  let lig := (actualCanonicalMolecule input.certified).ligandAtomAt center
  let x (k : Fin 4) : ℚ := param (lig k)
  have distinct (a b : Fin 4) (ne : a ≠ b) : x a ≠ x b := by
    intro eqn
    apply ne
    apply (actualCanonicalMolecule input.certified).ligandAtomAt_injective center
    apply param_injective
    change ((param (lig a) : Nat) : ℚ) = ((param (lig b) : Nat) : ℚ) at eqn
    exact_mod_cast eqn
  apply (centerAdmitted_iff _ _).mpr
  refine ⟨CartesianPoint3.orientedVolume (moment (x 0)) (moment (x 1)) (moment (x 2)) (moment (x 3)),?_,?_⟩
  · simp [coordinateVolume?,point,x,lig]
  · rw [volume]
    repeat' apply mul_ne_zero
    all_goals exact sub_ne_zero.mpr (distinct _ _ (by decide))

def original : input.certified.Atom := ⟨1,by decide +kernel⟩
abbrev Site := RingActivePairs.Site input
def path (q : Site) := q.val.node.history.map Fin.val
def sites := RingActiveDistanceSchedule.sites input

/-- The two real carbon-0 addresses: the direct edge and the route through
sulfur 2. Histories below follow the release's endpoint-to-original order. -/
def findSite? (history : List Nat) : Option Site := sites.find? fun q =>
  q.val.root == original && q.val.node.provenance == .realAtom && path q == history

def lowerS : Labels := (.pseudoasymmetric .s,.pseudoasymmetric .s)
def lowerR : Labels := (.pseudoasymmetric .r,.pseudoasymmetric .r)

/-- A publication derived from the distance evaluator at a genuine interior site
where a constitutional-only publication is unavailable. Blanking all deeper
publications loses the assignment. -/
structure Witness (history : List Nat) where
  site : Site
  originalRoot : site.val.root = original
  identified : path site = history
  real : site.val.node.provenance = .realAtom
  earlier : RingRetainedAuxiliary.publication? input site = none
  blank : RingNestedActivePair.publish? input site (fun _ => some none) = none
  issued : RingMolecularSchedule.atRoot input original site = some (some lowerS)

theorem Witness.derived {p} (w : Witness p) :
    RingMolecularSchedule.Derivation input w.site (some lowerS) :=
  RingMolecularSchedule.derivation w.site w.originalRoot w.issued

theorem Witness.genuinely_nested {p} (w : Witness p) :
    ∃ a : RingNestedActivePair.Assignment input w.site
        (RingNestedActivePair.masked w.site (RingMolecularSchedule.atRoot input original)),
      RingNestedActivePair.assign? input w.site
        (RingNestedActivePair.masked w.site (RingMolecularSchedule.atRoot input original)) = some a ∧
      a.labels = lowerS := by
  have published := (RingMolecularSchedule.atRoot_eq w.originalRoot).symm.trans w.issued
  rcases RingNestedActivePair.publication_source published with ⟨s,read,_⟩ | ranked
  · have hit := RingRetainedAuxiliary.publication_of_read read
    rw [w.earlier] at hit
    contradiction
  · obtain ⟨a,ha,labels⟩ := ranked
    exact ⟨a,ha,labels.symm⟩

private def witnessWith? (history : List Nat) (view : RingNestedActivePair.Reader input)
    (computed : view = RingMolecularSchedule.atRoot input original) : Option (Witness history) := do
  let q ← findSite? history
  if good : q.val.root = original ∧ path q = history ∧ q.val.node.provenance = .realAtom ∧
      RingRetainedAuxiliary.publication? input q = none ∧
      RingNestedActivePair.publish? input q (fun _ => some none) = none ∧ view q = some (some lowerS) then
    return ⟨q,good.1,good.2.1,good.2.2.1,good.2.2.2.1,good.2.2.2.2.1,computed ▸ good.2.2.2.2.2⟩
  else none

def witness? (history : List Nat) := witnessWith? history (RingMolecularSchedule.atRoot input original) rfl

private def expectedRequest : String :=
  String.intercalate "\n" (["centres-1.0"] ++
    molecule.atoms.map (fun a => s!"a {a.element.atomicNumber} 0 0") ++
    molecule.bonds.map (fun b => s!"b {b.source} {b.target}") ++
    ["f 0 R 1 2 3 5","f 1 R 0 2 17 21","f 3 S 0 4 7 8","f 4 R 3 9 10 11",
     "f 5 R 0 6 12 13","f 6 S 5 14 15 16","f 17 R 1 18 19 20","f 21 S 1 22 23 24"]) ++ "\n"

/-- Scores tabulated in physical atom order 1,2,3,5 at either original
address. The signs comparing 1 against 3 and 5 depend on the route; only
3 against 5 is doubled and reverses on reflection. -/
def pinnedMatrix (direct rev : Bool) : List Int :=
  let edge : Int := if direct then 1 else -1
  let pair : Int := if rev then -2 else 2
  [0,-1,edge,edge, 1,0,1,1, -edge,-1,0,pair, -edge,-1,-pair,0]

def differentPairs (a b : List Int) : List (Nat × Nat) :=
  let ids := [1,2,3,5]
  ([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)] : List (Nat × Nat)).filterMap fun (i,j) =>
    if decide (a[4*i+j]?.getD 0 > 0) != decide (b[4*i+j]?.getD 0 > 0) then some (ids[i]!,ids[j]!) else none

theorem parity_pattern :
    (∀ rev, differentPairs (pinnedMatrix true rev) (pinnedMatrix false rev) = [(1,3),(1,5)]) ∧
    (∀ direct, differentPairs (pinnedMatrix direct false) (pinnedMatrix direct true) = [(3,5)]) := by
  decide +kernel

private def byAtom {q : Site} {read : RingNestedActivePair.Reader input}
    (a : RingNestedActivePair.Assignment input q read) : Option (List Int × List Int) := do
  let slots ← ([1,2,3,5] : List Nat).mapM fun atom =>
    (List.finRange 4).find? fun k => a.frame.atoms [k] == [atom]
  let scores := slots.flatMap fun x => slots.map fun y => a.matrix.get x y
  return (scores.map Prod.fst,scores.map Prod.snd)

def validate : IO Unit := do
  let req ← IO.ofExcept (CentresRing.request input)
  unless req == expectedRequest do throw (IO.userError s!"source frame differs: {req}")
  let rule : RingActiveDistanceSchedule.Rule input := fun q before =>
    if q.val.root = original then RingNestedActivePair.publish? input q before else none
  let table := RingActiveDistanceSchedule.table rule
    (RingActiveDistanceSchedule.height input + 1)
  let view := RingActiveDistanceSchedule.snapshot table
  have computed : view = RingMolecularSchedule.atRoot input original :=
    RingActiveDistanceSchedule.snapshot_table _ _
  let get (p : List Nat) : IO Site := do
    let some q := findSite? p | throw (IO.userError s!"missing original-root occurrence {p}")
    return q
  for (p,expected) in [([3,0,1],RS.R),([4,3,0,1],.R),([5,0,1],.S),([6,5,0,1],.S),
      ([3,0,2,1],.R),([4,3,0,2,1],.R),([5,0,2,1],.S),([6,5,0,2,1],.S)] do
    let q ← get p
    unless view q == some (some (.chiral expected,.chiral expected.swap)) do
      throw (IO.userError s!"unexpected deeper publication {p}: {repr (view q)}")
  for p in [[0,1],[0,2,1]] do
    let q ← get p
    let some _ := witnessWith? p view computed |
      throw (IO.userError s!"old={repr (RingRetainedAuxiliary.publication? input q)}, blank={repr (RingNestedActivePair.publish? input q (fun _ => some none))}, new={repr (view q)} at {p}")
    let some a := RingNestedActivePair.assign? input q (RingNestedActivePair.masked q view) |
      throw (IO.userError s!"missing nested ranking at {p}")
    let direct := p == [0,1]
    let raw := a.frame.atoms a.actual.slots
    let refl := a.frame.atoms a.reflected.slots
    let sourceRaw := if direct then [2,1,3,5] else [2,3,5,1]
    let sourceRefl := if direct then [2,1,5,3] else [2,5,3,1]
    unless raw == sourceRaw && refl == sourceRefl &&
      byAtom a == some (pinnedMatrix direct false,pinnedMatrix direct true) do
      throw (IO.userError s!"unexpected orders/scores {p}: {raw}, {refl}, {repr (byAtom a)}")
    IO.println s!"original C1: {p} publishes (s,s), orders {raw}/{refl}, both 16 scores agree; blank view and constitutional-only both fail"
  let q ← get [1]
  unless view q == some (some lowerR) do
    throw (IO.userError s!"unexpected outer assignment: {repr (view q)}")
  IO.println "original C1 gives (r,r) after the deeper publications"
  let parent ← get [0,2,1]
  let some copy := (RingRetainedAuxiliary.frame input.certified parent).find? (fun arm =>
      path arm.occurrence == [1,0,2,1] && arm.occurrence.val.node.provenance == .ringDuplicate 0) |
    throw (IO.userError "missing retained closure of the original carbon")
  unless (input.certified.executableLocalizedRerootChildren copy).isEmpty &&
      RingActivePairs.z? input copy == some 6 && view copy.occurrence == some none do
    throw (IO.userError "ring closure of the original carbon failed its Z/absence test")
  let mut positive : Nat := 0
  let mut absent : Nat := 0
  let mut missing : List (List Nat) := []
  for q in sites do
    if q.val.root == original then
      match view q with
      | some (some _) => positive := positive + 1
      | some none => absent := absent + 1
      | none => missing := path q :: missing
  IO.println s!"original C1 occurrence census: {positive} published, {absent} known absent, {missing.length} unresolved; first unresolved histories {missing.reverse.take 8}"


end TetraStereo.Examples.RingNestedPublication

assert_kernel_only TetraStereo.Examples.RingNestedPublication.admitted
assert_kernel_only TetraStereo.Examples.RingNestedPublication.calibrated
assert_kernel_only TetraStereo.Examples.RingNestedPublication.Witness.derived
assert_kernel_only TetraStereo.Examples.RingNestedPublication.Witness.genuinely_nested
assert_kernel_only TetraStereo.Examples.RingNestedPublication.parity_pattern
