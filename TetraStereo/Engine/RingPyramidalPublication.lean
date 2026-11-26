import TetraStereo.Engine.RingOxaziridineNitrogen
import TetraStereo.Engine.RingFullPathConstitution
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames

/-! P-93.3.4.1 supplies a lowest-priority phantom at a pyramidal phosphorus.
The phantom is local to the coordinate frame. Only bonded atoms enter the digraph. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingPyramidalPublication
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Arm Site)
open RingActiveDistanceSchedule (View Cell)
open RingNestedActivePair (Labels consistent)
open RingFullPathEligibility (Key)
open RingRetainedChemicalTrace (Word)

/-- Neutral, nonaromatic three-coordinate P/As/Sb centers and structurally
selected bridgehead or N-alkyl oxaziridine nitrogen, after attached hydrogens have been materialized.
The legacy name remains a compatibility interface. -/
def phosphorus (i : Input) (a : i.certified.Atom) : Bool :=
  (i.molecule.atoms[a.val]?).any (fun atom =>
    ((atom.element == .P || atom.element == .As || atom.element == .Sb) ||
      (atom.element == .N && RingPyramidalNitrogen.constrained i a)) && atom.charge == 0 && !atom.aromatic) &&
    decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3)

/-- Runtime selection checks cheap records and candidate elements before degree,
and checks the nitrogen topology only for otherwise eligible nitrogen. -/
def phosphorusFast (i : Input) (a : i.certified.Atom) : Bool :=
  (i.molecule.atoms[a.val]?).any fun atom =>
    atom.charge == 0 && !atom.aromatic &&
    (atom.element == .P || atom.element == .As || atom.element == .Sb || atom.element == .N) &&
    decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3) &&
    ((atom.element == .P || atom.element == .As || atom.element == .Sb) ||
      (atom.element == .N && RingPyramidalNitrogen.constrained i a))

@[csimp] theorem phosphorus_fast : @phosphorus = @phosphorusFast := by
  funext i a
  unfold phosphorus phosphorusFast
  cases lookup : i.molecule.atoms[a.val]? with
  | none => rfl
  | some atom =>
    apply Bool.eq_iff_iff.mpr
    simp only [Option.any_some,Bool.and_eq_true,Bool.or_eq_true]
    aesop

def eligible (i : Input) (a : i.certified.Atom) : Bool :=
  decide (Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4) || phosphorus i a

def focusP (i : Input) (q : Site i) : Option i.certified.Atom :=
  if q.val.node.provenance = .realAtom then q.val.node.current?.filter (phosphorus i) else none

/-- At a selected phosphorus every physical neighbor contributes exactly one
direction, including the parent direction of an auxiliary occurrence. -/
theorem focusP_neighbors {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : focusP i q = some a) :
    ∃ bij : {t // t ∈ RingRetainedAuxiliary.frame i.certified q} ≃ i.certified.moleculeGraph.Neighbor a,
      (∀ t, t.1.occurrence.val.node.current? = some (bij t).1) ∧
      (RingRetainedAuxiliary.frame i.certified q).length = 3 := by
  unfold focusP at selected
  split at selected <;> try contradiction
  rename_i real
  obtain ⟨atAtom,ok⟩ := Option.filter_eq_some_iff.mp selected
  obtain ⟨cs,bij,computed,physical⟩ :=
    i.certified.simpleBond_realAtom_rerootChildren_neighborEquiv i.single (Nat.le_succ _) q a ⟨real,atAtom⟩
  have same : cs = RingRetainedAuxiliary.frame i.certified q := Option.some.inj
    (computed.symm.trans (i.certified.localizedRerootChildren?_eq_some_executable _))
  subst cs
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
    simp only [phosphorus,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact ok.2
  exact ⟨bij,physical,(i.certified.simpleBond_realAtom_rerootChildren_length_eq_neighbor_card
    i.single (Nat.le_succ _) q a ⟨real,atAtom⟩ _ computed).trans degree⟩

/-- Extend the ray from the centroid of the three bonded ligands through P.
This computation supplies a witness on the phantom side of their plane. -/
def phantomPoint (a b c p : CartesianPoint3) : CartesianPoint3 :=
  ⟨4*p.x-a.x-b.x-c.x, 4*p.y-a.y-b.y-c.y, 4*p.z-a.z-b.z-c.z⟩

theorem phantom_hand (a b c p : CartesianPoint3) :
    descriptorOfPriorityOrderedPoints? [a,b,c,phantomPoint a b c p] =
      descriptorOfPriorityOrderedPoints? [a,b,c,p] := by
  have volume : CartesianPoint3.orientedVolume a b c (phantomPoint a b c p) =
      4 * CartesianPoint3.orientedVolume a b c p := by
    simp only [CartesianPoint3.orientedVolume,phantomPoint]
    ring
  simp only [descriptorOfPriorityOrderedPoints?,volume,descriptorOfOrientedVolume?]
  split_ifs <;> first | rfl | linarith

structure Ligand (i : Input) where
  arm : Arm i
  atom : Nat
  priority : Key

/-- Read each of the three molecular directions in the existing digraph,
including the incoming direction when the phosphorus is auxiliary. -/
def ligands? (i : Input) (q : Site i) (r : View i) (rev : Bool) :=
  (RingRetainedAuxiliary.frame i.certified q).mapM fun arm => do
    let atom ← arm.occurrence.val.node.current?
    let priority ← RingFullPathEligibility.key? i r rev arm
    return (⟨arm,atom.val,priority⟩ : Ligand i)

def trial? {i : Input} (r : View i) (a : i.certified.Atom) (rev : Bool)
    (xs : List (Ligand i)) (mark : Option Nat) : Option (Option RS) := do
  let rows ← xs.mapM fun x => do
    let word ← match mark with
      | none => some ([] : Word)
      | some id => (RingGroupedMark.arm? i r id x.arm).map fun b => b.2.word
    return (x.atom,RingFullPathTrialReadings.trialKey x.priority word)
  if !(rows.map Prod.snd).Nodup then return none
  let ordered := RingStereoSiblingPass.order Prod.snd rows
  let g := inputGeometry i.certified
  -- Using P itself as the fourth determinant point gives exactly the sign
  -- of a phantom on the P side of the plane of the three bonded ligands.
  return readback? (if rev then mirror g else g) (ordered.map Prod.fst ++ [a.val])

def hands? (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) (rev : Bool) :
    Option (List (Option RS)) := do
  let xs ← ligands? i q r rev
  -- With a permanently lowest phantom, three tied slots means all real
  -- ligands tie. A single tied pair receives only the ordinary trial.
  let marks : List (Option Nat) := match xs with
    | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
        [some x.atom,some y.atom,some z.atom] else [none]
    | _ => []
  marks.mapM (trial? r a rev xs)

def pLabels (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) : Option Labels := do
  guard ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  let hs ← hands? i q r a false
  let ms ← hands? i q r a true
  RingFullPathPublication.crossed hs ms

theorem pLabels_consistent (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) :
    (pLabels i q r a).all RingNestedActivePair.consistent = true := by
  unfold pLabels
  by_cases shape : (RingRetainedAuxiliary.frame i.certified q).length = 3
  · simp only [shape,guard,if_true,pure,bind,Option.bind]
    cases hands? i q r a false <;> cases hands? i q r a true <;> try rfl
    rename_i hs ms
    change (RingFullPathPublication.crossed hs ms).all RingNestedActivePair.consistent = true
    unfold RingFullPathPublication.crossed
    cases RingChemicalPriority.ReferenceFrame.survivingHand (LocalizedChemicalRingPromotionAggregation.readingBalance hs) with
    | none => rfl
    | some h =>
      cases RingChemicalPriority.ReferenceFrame.survivingHand (LocalizedChemicalRingPromotionAggregation.readingBalance ms) with
      | none => rfl
      | some m => cases h <;> cases m <;> rfl
  · simp [shape,guard]

def publish (i : Input) (q : Site i) (r : View i) : Cell :=
  match focusP i q with
  | some a => some (pLabels i q r a)
  | none => RingFullPathConstitution.fastPublish i q r

end TetraStereo.Engine.RingPyramidalPublication

assert_kernel_only TetraStereo.Engine.RingPyramidalPublication.phantom_hand
assert_kernel_only TetraStereo.Engine.RingPyramidalPublication.pLabels_consistent
assert_kernel_only TetraStereo.Engine.RingPyramidalPublication.focusP_neighbors

assert_kernel_only TetraStereo.Engine.RingPyramidalPublication.phosphorus_fast
