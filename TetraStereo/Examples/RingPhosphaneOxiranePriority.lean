import TetraStereo.Examples.RingPhosphaneOxiraneStore
import TetraStereo.Examples.RingDeuteratedCyclopropanePriority
import Batteries.Tactic.OpenPrivate

/-! Kernel-certified native full-path keys at the C0 focus of phosphane oxirane.
The fixed reference supplies graph data only. Final focus readback remains an arbitrary geometry.
The opposite P auxiliary hands are supplied by the exact canonical frozen reader. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace TetraStereo.Engine.RingHydrogenSpelling.PhosRootKey
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)

def molecule : RawMolecule := PhosphaneOxirane.molecule

def referencePoints : SpatialConfiguration := ⟨List.replicate 11 ⟨0,0,0⟩⟩
theorem reference_exists : (LocalizedChemicalRing.admitRawSpatial? molecule referencePoints).isSome = true := by decide +kernel

def reference : Input := (LocalizedChemicalRing.admitRawSpatial? molecule referencePoints).get reference_exists

theorem reference_size : reference.certified.certified.input.molecule.atomCount = 11 := by decide +kernel

def atom (n : Fin 11) : reference.certified.Atom := Fin.cast reference_size.symm n

def originOrder? (a : Fin 11) : Option (List Nat) :=
  (RingRetainedAuxiliary.order reference.certified (RingGroupedReport.origin reference (atom a))).mapM RingRetainedAuxiliary.atom?

def origin (n : Fin 11) := RingGroupedReport.origin reference (atom n)

def neighborIDs (n : Fin 11) : List (Fin 11) :=
  match n.val with
  | 0 => [1,2,3,4]
  | 1 => [0,5,6]
  | 2 => [0,7,8]
  | 3 => [0,4]
  | 4 => [0,3,9,10]
  | 5 | 6 => [1]
  | 7 | 8 => [2]
  | _ => [4]

theorem neighbors_sorted (n : Fin 11) :
    (reference.certified.moleculeGraph.neighborFinset (atom n)).sort (· ≤ ·) = (neighborIDs n).map atom := by
  have setEq : reference.certified.moleculeGraph.neighborFinset (atom n) = ((neighborIDs n).map atom).toFinset := by
    ext a
    rw [reference.certified.moleculeGraph.mem_neighborFinset]
    revert a
    fin_cases n <;> decide +kernel
  rw [setEq]
  fin_cases n <;> apply (List.toFinset_sort (· ≤ ·) (by decide +kernel)).mpr <;> decide +kernel

def fastNeighborCopies (a : reference.certified.Atom) :=
  (neighborIDs (Fin.cast reference_size a)).flatMap fun n =>
    (List.range (reference.certified.moleculeGraph.bond a (atom n))).map fun k => (atom n,k)

theorem neighborCopies_eq (a : reference.certified.Atom) :
    reference.certified.executableOfficialNeighborCopies a = fastNeighborCopies a := by
  have aeq : a = atom (Fin.cast reference_size a) := rfl
  conv_lhs => rw [aeq]
  unfold executableOfficialNeighborCopies
  rw [neighbors_sorted,List.flatMap_map]
  rfl

def fastChildCopies (node : OfficialCIPNode reference.certified.Atom) :=
  match node.current? with
  | none => []
  | some a => match node.parent? with
    | none => fastNeighborCopies a
    | some parent => (fastNeighborCopies a).filter fun copy => !(copy.1 == parent && copy.2 == 0)

def fastChildren (node : OfficialCIPNode reference.certified.Atom) :=
  if node.isDuplicateLeaf then [] else (fastChildCopies node).map fun copy => node.extend copy.1 copy.2

theorem children_eq (node : OfficialCIPNode reference.certified.Atom) :
    reference.certified.executableOfficialCIPChildren node = fastChildren node := by
  unfold executableOfficialCIPChildren fastChildren executableOfficialChildCopies fastChildCopies
  cases node.current? <;> cases node.parent? <;> simp only [neighborCopies_eq]

def fastSubtree (root : reference.certified.Atom) : Nat → List Nat →
    OfficialCIPNode reference.certified.Atom → List reference.certified.LocalizedCIPOccurrenceFrame
  | 0,path,node => [⟨root,path,node,0⟩]
  | fuel+1,path,node => ⟨root,path,node,fuel+1⟩ ::
      (fastChildren node).zipIdx.flatMap fun child => fastSubtree root fuel (path++[child.2]) child.1

theorem subtree_eq (root : reference.certified.Atom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode reference.certified.Atom) :
    reference.certified.localizedOccurrenceSubtree root fuel path node = fastSubtree root fuel path node := by
  induction fuel generalizing path node with
  | zero => rfl
  | succ fuel ih =>
    simp only [localizedOccurrenceSubtree,fastSubtree,children_eq]
    congr 1
    apply List.flatMap_congr
    intro child _
    exact ih _ _

def fastOccurrences (fuel : Nat) :=
  ((List.finRange reference.certified.certified.input.molecule.atomCount).flatMap
    fun root => fastSubtree root (fuel+1) [] (OfficialCIPNode.root root)).dedup

theorem occurrences_eq (fuel : Nat) : reference.certified.localizedOccurrences fuel = fastOccurrences fuel := by
  unfold localizedOccurrences localizedOccurrencesAtAtom fastOccurrences
  simp only [subtree_eq]

def fastIntended {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :=
  let neighbors := ((fastOccurrences fuel).filter fun c => c.root == cursor.occurrence.val.root &&
    c.address.length+1 == cursor.occurrence.val.address.length && c.address == cursor.occurrence.val.address.dropLast) ++
    ((fastOccurrences fuel).filter fun c => c.root == cursor.occurrence.val.root &&
      c.address.length == cursor.occurrence.val.address.length+1 && c.address.dropLast == cursor.occurrence.val.address)
  if cursor.occurrence.val.node.isDuplicateLeaf then [] else match cursor.previous? with
    | none => neighbors
    | some previous => neighbors.filter fun f => f.address != previous.val.address

theorem intended_eq {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :
    reference.certified.intendedLocalizedRerootChildFrames cursor = fastIntended cursor := by
  unfold intendedLocalizedRerootChildFrames localizedRerootNeighborFrames localizedCarrierParentFrames
    localizedCarrierOutwardChildFrames fastIntended
  cases cursor.previous? <;> simp only [occurrences_eq]

def fastRerootChildren {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :=
  (fastIntended cursor).attach.map fun f =>
    ({ occurrence := ⟨f.val, reference.certified.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
        cursor f.val (by rw [intended_eq]; exact f.property)⟩
       previous? := some cursor.occurrence } : reference.certified.LocalizedRerootCursor fuel)

theorem rerootChildren_eq {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :
    reference.certified.executableLocalizedRerootChildren cursor = fastRerootChildren cursor := by
  unfold executableLocalizedRerootChildren fastRerootChildren
  rw [List.attach_congr (intended_eq cursor),List.map_map]
  apply List.map_congr_left
  intro frame _
  rfl

theorem neighborSort_eq (a : reference.certified.Atom) :
    (reference.certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) =
      (neighborIDs (Fin.cast reference_size a)).map atom := by
  have aeq : a = atom (Fin.cast reference_size a) := rfl
  conv_lhs => rw [aeq]
  exact neighbors_sorted _

def centerZero : reference.certified.TetrahedralCenter := ⟨atom 0, by decide +kernel⟩

theorem zero_four : (RingRetainedAuxiliary.frame reference.certified (origin 0)).length = 4 := by
  unfold RingRetainedAuxiliary.frame
  rw [rerootChildren_eq]
  decide +kernel

theorem zero_atoms : (RingRetainedAuxiliary.frame reference.certified (origin 0)).mapM
    (fun q => q.occurrence.val.node.current?.map Fin.val) = some [1,2,3,4] := by
  unfold RingRetainedAuxiliary.frame
  rw [rerootChildren_eq]
  decide +kernel

theorem zero_canonical : RingRetainedAuxiliary.canonical reference.certified centerZero = [1,2,3,4] := by
  unfold RingRetainedAuxiliary.canonical canonicalLigandAtom canonicalNeighborList
  simp only [centerZero]
  have getD (k : Fin ((reference.certified.moleculeGraph.neighborFinset (atom 0)).sort (· ≤ ·)).length) :
      ((reference.certified.moleculeGraph.neighborFinset (atom 0)).sort (· ≤ ·)).get k =
      ((neighborIDs 0).map atom).getD k.val (atom 0) := by
    rw [← List.getD_eq_get (d := atom 0)]
    exact congrArg (fun xs : List reference.certified.Atom => xs.getD k.val (atom 0)) (neighbors_sorted 0)
  simp only [getD]
  decide +kernel

def frameZero : RingNestedActivePair.Frame reference (origin 0) where
  center := centerZero
  recognized := (reference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mpr ⟨rfl,rfl⟩
  four := zero_four
  ids := [1,2,3,4]
  actualAtoms := zero_atoms
  physical := by rw [zero_canonical]

open private build from TetraStereo.Engine.RingRetainedChemicalTrace
open RingRetainedChemicalTrace

def fastAssemble (o : Observation) (ks : List Key) : Key := IsotopeOrder.fastAssemble o ks

theorem assemble_eq (o : Observation) (ks : List Key) : assemble o ks = fastAssemble o ks :=
  IsotopeOrder.assemble_eq o ks

def fastBuild {d : Nat} : Nat → reference.certified.LocalizedRerootCursor d → Option Key
  | 0,_ => none
  | n+1,q => do
    let cs := fastRerootChildren q
    let root ← observation? reference q cs.isEmpty
    let keys ← cs.mapM (fastBuild n)
    return fastAssemble root keys

private theorem build_eq {d : Nat} (n : Nat) (q : reference.certified.LocalizedRerootCursor d) :
    build reference reference.certified.executableLocalizedRerootChildren n q = fastBuild n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change (do
      let cs := reference.certified.executableLocalizedRerootChildren q
      let root ← observation? reference q cs.isEmpty
      let keys ← cs.mapM (build reference reference.certified.executableLocalizedRerootChildren n)
      pure (assemble root keys)) = _
    have recEq : build reference reference.certified.executableLocalizedRerootChildren n = fastBuild n := funext ih
    simp only [rerootChildren_eq,recEq,assemble_eq]
    rfl

theorem key_eq {d : Nat} (q : reference.certified.LocalizedRerootCursor d) :
    key? reference q = fastBuild (2*(d+1)+1) q := build_eq _ _

def fastArm (n : Fin 11) (k : RingActivePairReport.Slot) :=
  (fastRerootChildren ⟨origin n,none⟩).getD k.val ⟨origin n,none⟩

theorem arm_eq {n : Fin 11} (fr : RingNestedActivePair.Frame reference (origin n))
    (k : RingActivePairReport.Slot) : fr.arm k = fastArm n k := by
  unfold RingNestedActivePair.Frame.arm
  rw [← List.getD_eq_get (d := ⟨origin n,none⟩)]
  change (reference.certified.executableLocalizedRerootChildren ⟨origin n,none⟩).getD k.val ⟨origin n,none⟩ = _
  exact congrArg (fun xs => xs.getD k.val ⟨origin n,none⟩) (rerootChildren_eq ⟨origin n,none⟩)

def fastWord (n : Fin 11) (k : RingActivePairReport.Slot) : List Word :=
  ((fastBuild (2*((reference.certified.certified.input.molecule.atomCount+1)+1)+1)
    ⟨(fastArm n k).occurrence,some (origin n)⟩).map RingRetainedChemicalPreorder.orderWord).getD []

theorem word_eq {n : Fin 11} (fr : RingNestedActivePair.Frame reference (origin n))
    (k : RingActivePairReport.Slot) : RingFullPathConstitution.word fr k = fastWord n k := by
  have read := RingRetainedChemicalPreorder.read_key (fr.direction k)
  rw [key_eq] at read
  change fastBuild _ ⟨(fr.arm k).occurrence,some (origin n)⟩ = some _ at read
  rw [arm_eq] at read
  unfold RingFullPathConstitution.word fastWord
  rw [read]
  rfl


open LocalizedGenericMarkedRecalculation
open RingNestedActivePair (Reader Labels consistent)
open RingActivePairs (Arm Site)
open RingStereoSiblingPass (Branch)

theorem reference_molecule : reference.molecule = PhosphaneOxirane.molecule := by decide +kernel

def canonicalStore := PhosphaneOxirane.canonicalStore reference

def canonicalReader (h1 h2 : Option OneCenter.RS) : Reader reference :=
  PhosphaneOxirane.canonicalReader reference reference_molecule h1 h2

def reader : Reader reference := canonicalReader (some .R) (some .S)

def fastUnit : Nat → Arm reference → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← fastBuild (2*((reference.certified.certified.input.molecule.atomCount+1)+1)+1) q
    let labels ← reader q.occurrence
    guard (labels.all RingNestedActivePair.consistent = true ∧ (fastRerootChildren q = [] → labels = none))
    let cs ← (fastRerootChildren q).mapM (fastUnit n)
    return RingRetainedUnitPass.branch k (RingNestedActivePair.unit (labels.map Prod.fst))
      (KernelSort.sort cs (fun a b => decide (Branch.shallow b ≤ Branch.shallow a)))
      (KernelSort.sort cs (fun a b => decide (Branch.deep b ≤ Branch.deep a)))

theorem unit_eq (n : Nat) (q : Arm reference) : RingRetainedUnitPass.build reference reader n q = fastUnit n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedUnitPass.build,fastUnit,key_eq,rerootChildren_eq,
      RingStereoSiblingPass.order,KernelSort.function_eq]
    have eq : RingRetainedUnitPass.build reference reader n = fastUnit n := funext ih
    rw [eq]

def fastRefine (prior : Arm reference → Option Branch)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool) : Nat → Arm reference → Option Branch
  | 0,_ => none
  | n+1,q => do
    let p ← prior q
    let v ← reader q.occurrence
    let cs ← (fastRerootChildren q).mapM (fastRefine prior obs rev n)
    return RingRetainedStereoRefinement.extend p (obs.value v rev)
      (KernelSort.sort cs (fun a b => decide (Branch.shallow b ≤ Branch.shallow a)))
      (KernelSort.sort cs (fun a b => decide (Branch.deep b ≤ Branch.deep a)))

theorem refine_eq (prior : Arm reference → Option Branch)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool) (n : Nat) (q : Arm reference) :
    RingRetainedStereoRefinement.build reference prior reader obs rev n q = fastRefine prior obs rev n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedStereoRefinement.build,fastRefine,rerootChildren_eq,
      RingStereoSiblingPass.order,KernelSort.function_eq]
    have eq : RingRetainedStereoRefinement.build reference prior reader obs rev n = fastRefine prior obs rev n := funext ih
    rw [eq]

def fastPriority (rev : Bool) : List RingRetainedStereoRefinement.Observation → Arm reference → Option Branch
  | [],q => fastUnit (reference.certified.localizedRerootCursorBudget q+1) q
  | o::os,q => fastRefine (fastPriority rev os) o rev (reference.certified.localizedRerootCursorBudget q+1) q

theorem priority_eq (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) :
    RingRetainedStereoRefinement.priority reference reader rev os = fastPriority rev os := by
  induction os with
  | nil => funext q; exact unit_eq _ _
  | cons o os ih =>
    funext q
    simp only [RingRetainedStereoRefinement.priority,fastPriority,ih,refine_eq]

def fastSphere {β κ : Type} [LinearOrder κ] (key : β → κ) (next : β → Option (List β)) :
    Nat → List β → Option (List β)
  | _,[] => some []
  | 0,_::_ => none
  | n+1,x::xs => do
    let blocks ← (x::xs).mapM next
    return (x::xs) ++ (← fastSphere key next n (KernelSort.sort blocks.flatten (fun a b => decide (key b ≤ key a))))

theorem sphere_eq {β κ : Type} [LinearOrder κ] (key : β → κ) (next : β → Option (List β))
    (n : Nat) (row : List β) : RingFullPathPairs.sphereRun key next n row = fastSphere key next n row := by
  induction n generalizing row with
  | zero => cases row <;> rfl
  | succ n ih =>
    cases row with
    | nil => rfl
    | cons x xs =>
      simp only [RingFullPathPairs.sphereRun,fastSphere,RingStereoSiblingPass.order,KernelSort.function_eq]
      have eq : RingFullPathPairs.sphereRun key next n = fastSphere key next n := funext ih
      rw [eq]

def fastNext (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : OneCenter.RS)
    (p : RingFullPathPairs.FullVisit reference) : Option (List (RingFullPathPairs.FullVisit reference)) :=
  (fastRerootChildren p.cursor).mapM fun c => do
    let k ← fastPriority rev os c
    return ⟨c,p.path ++ [RingFullPathPairs.stepKey k.deep (RingFullPathPairs.likeAt reference reader rev seed c)]⟩

def fastStage (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : OneCenter.RS)
    (q : Arm reference) : Option (List Bool) :=
  (fastSphere RingFullPathPairs.FullVisit.path (fastNext rev os seed)
    (reference.certified.localizedRerootCursorBudget q+1) [RingFullPathPairs.rootVisit reference reader rev seed q]).map
    fun out => out.filterMap fun v => RingFullPathPairs.likeAt reference reader rev seed v.cursor

theorem stage_eq (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : OneCenter.RS)
    (q : Arm reference) : RingFullPathPairs.stageWords reference reader rev os seed q = fastStage rev os seed q := by
  unfold RingFullPathPairs.stageWords RingFullPathPairs.Oracle.bits? RingFullPathPairs.Oracle.visits?
  rw [sphere_eq]
  have nextEq : (RingFullPathPairs.stage reference reader rev os).next?
      (RingFullPathPairs.likeAt reference reader rev seed) = fastNext rev os seed := by
    funext p
    simp only [RingFullPathPairs.Oracle.next?,RingFullPathPairs.stage,priority_eq,fastNext,rerootChildren_eq]
  rw [nextEq]
  rfl

def arm (k : RingActivePairReport.Slot) : Arm reference :=
  ⟨(fastArm 0 k).occurrence,some (origin 0)⟩

theorem cursor_eq (k : RingActivePairReport.Slot) : RingGroupedCentre.cursor frameZero k = arm k := by
  change (⟨(frameZero.arm k).occurrence,some (origin 0)⟩ : Arm reference) = _
  rw [arm_eq]
  rfl

theorem rule5_p1 : RingFullPathRule5.word? reference reader false .R (RingGroupedCentre.cursor frameZero 0) = some [true] := by
  unfold RingFullPathRule5.word?
  rw [stage_eq,cursor_eq]
  decide +kernel

theorem rule5_p2 : RingFullPathRule5.word? reference reader false .R (RingGroupedCentre.cursor frameZero 1) = some [false] := by
  unfold RingFullPathRule5.word?
  rw [stage_eq,cursor_eq]
  decide +kernel

def fastFullKey (rev : Bool) (q : Arm reference) : Option RingFullPathEligibility.Key := do
  let u ← fastPriority rev [] q
  let l ← fastPriority rev [.lowercase] q
  let ar ← fastStage rev [] .R q
  let as' ← fastStage rev [] .S q
  let fr ← fastStage rev [.lowercase] .R q
  return ⟨u.deep,max ar as',l.word,fr⟩

theorem fullKey_eq (rev : Bool) (q : Arm reference) :
    RingFullPathEligibility.key? reference reader rev q = fastFullKey rev q := by
  unfold RingFullPathEligibility.key? fastFullKey RingFullPathPairs.pairs? RingFullPathRule5.word?
  simp only [priority_eq,stage_eq]

/-- Explicit native key data; the equations below certify it against the evaluator. -/
def phosphorusKey (bit : Bool) : RingFullPathEligibility.Key := {
  throughFourA := [[[15], [17, 9], [17, 9], [], [], [], []],
                    [[0], [0, 0], [0, 0], [], [], [], []],
                    [[30973761997680],
                     [35450000000000, 18998403162070],
                     [35450000000000, 18998403162070],
                     [],
                     [],
                     [],
                     []],
                    [[2], [0, 0], [0, 0], [], [], [], []]]
  bestFourB := [true]
  fourC := [[0], [0, 0], [0, 0], [], [], [], []]
  fixedR := [bit] }

def oxygenKey : RingFullPathEligibility.Key := {
  throughFourA := [[[8], [6], [6], [6, 1, 1], [6, 1, 1], [], [], [], [], [], []],
                    [[0], [0], [0], [12, 0, 0], [12, 0, 0], [], [], [], [], [], []],
                    [[15999000000000],
                     [12011000000000],
                     [12011000000000],
                     [12011000000000, 1007825031898, 1007825031898],
                     [12011000000000, 1007825031898, 1007825031898],
                     [],
                     [],
                     [],
                     [],
                     [],
                     []],
                    [[0], [0], [0], [0, 0, 0], [0, 0, 0], [], [], [], [], [], []]]
  bestFourB := []
  fourC := [[0], [0], [0], [0, 0, 0], [0, 0, 0], [], [], [], [], [], []]
  fixedR := [] }

def carbonKey : RingFullPathEligibility.Key := {
  throughFourA := [[[6], [8, 1, 1], [8, 1, 1], [6], [6], [], [], [], [], [], []],
                    [[0], [0, 0, 0], [0, 0, 0], [12], [12], [], [], [], [], [], []],
                    [[12011000000000],
                     [15999000000000, 1007825031898, 1007825031898],
                     [15999000000000, 1007825031898, 1007825031898],
                     [12011000000000],
                     [12011000000000],
                     [],
                     [],
                     [],
                     [],
                     [],
                     []],
                    [[0], [0, 0, 0], [0, 0, 0], [0], [0], [], [], [], [], [], []]]
  bestFourB := []
  fourC := [[0], [0, 0, 0], [0, 0, 0], [0], [0], [], [], [], [], [], []]
  fixedR := [] }

def keys (rev : Bool) (k : RingActivePairReport.Slot) : RingFullPathEligibility.Key :=
  ![phosphorusKey (!rev),phosphorusKey rev,oxygenKey,carbonKey] k

theorem fullKey_literal (rev : Bool) (k : RingActivePairReport.Slot) :
    fastFullKey rev (arm k) = some (keys rev k) := by
  cases rev <;> fin_cases k <;> decide +kernel

def trialWord (rev : Bool) (k : RingActivePairReport.Slot) : List (List Word) :=
  RingFullPathTrialReadings.trialKey (keys rev k) []

theorem actual_descending : (([0,1,2,3] : List RingActivePairReport.Slot).map (trialWord false)).Pairwise (· > ·) := by
  decide +kernel

theorem reflected_descending : (([1,0,2,3] : List RingActivePairReport.Slot).map (trialWord true)).Pairwise (· > ·) := by
  decide +kernel

theorem keys_native (rev : Bool) : RingFullPathPublication.keys? frameZero reader rev = some (keys rev) := by
  have hit (k : RingActivePairReport.Slot) :
      RingFullPathEligibility.key? reference reader rev (RingGroupedCentre.cursor frameZero k) = some (keys rev k) := by
    rw [fullKey_eq,cursor_eq]
    exact fullKey_literal rev k
  unfold RingFullPathPublication.keys? RingActivePairReport.four?
  simp only [hit,Option.bind_eq_bind,Option.bind_some]
  congr 1

theorem trialWord_eq (rev : Bool) (k : RingActivePairReport.Slot) :
    trialWord rev k = RingFullPathTrialReadings.trialKey (keys rev k) [] := rfl

theorem actual_legal : RingStereoSiblingPass.Legal
    (fun k => RingFullPathTrialReadings.trialKey (keys false k) []) (List.finRange 4) [0,1,2,3] := by
  refine ⟨by decide +kernel,?_⟩
  have eq : trialWord false = fun k => RingFullPathTrialReadings.trialKey (keys false k) [] := funext (trialWord_eq false)
  rw [←eq]
  exact actual_descending.imp (fun h => le_of_lt h)

theorem reflected_legal : RingStereoSiblingPass.Legal
    (fun k => RingFullPathTrialReadings.trialKey (keys true k) []) (List.finRange 4) [1,0,2,3] := by
  refine ⟨by decide +kernel,?_⟩
  have eq : trialWord true = fun k => RingFullPathTrialReadings.trialKey (keys true k) [] := funext (trialWord_eq true)
  rw [←eq]
  exact reflected_descending.imp (fun h => le_of_lt h)

theorem before5_tie : ∀ rev : Bool,
    (fastFullKey rev (arm 0)).map (fun k => (k.throughFourA,k.bestFourB,k.fourC)) =
      (fastFullKey rev (arm 1)).map (fun k => (k.throughFourA,k.bestFourB,k.fourC)) := by
  intro rev
  rw [fullKey_literal,fullKey_literal]
  cases rev <;> decide +kernel

theorem one_trial : RingFullPathTrialReadings.trials (keys false) = [none] := by decide +kernel

theorem one_reversal : RingFullPathPublication.reversals (keys false) (keys true) = 1 := by decide +kernel

theorem centre_abstract (read : (RingActivePairReport.Slot → List (List Word)) → Option OneCenter.RS) :
    RingFrameTransport.centreG frameZero reader read =
      some (RingFullPathPublication.letters (keys false) (keys true)
        [read (fun k => RingFullPathTrialReadings.trialKey (keys false k) [])]) := by
  unfold RingFrameTransport.centreG RingFrameTransport.readingsG
  change (RingFullPathPublication.keys? frameZero reader false).bind _ = _
  rw [keys_native false]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [keys_native true]
  simp only [Option.bind_some]
  change ((RingFullPathPublication.keys? frameZero reader false).bind _).map _ = _
  rw [keys_native false]
  simp only [Option.bind_some]
  unfold RingFrameTransport.readingsWithG
  rw [one_trial]
  simp [RingFullPathTrialReadings.markWords?]

theorem letters_rule5 (h : Option OneCenter.RS) :
    RingFullPathPublication.letters (keys false) (keys true) [h] =
      h.map (fun h => (.pseudoasymmetric (pseudoRSOfRS h),.pseudoasymmetric (pseudoRSOfRS h))) := by
  unfold RingFullPathPublication.letters
  rw [one_reversal]
  cases h with
  | none => rfl
  | some h => cases h <;> rfl

theorem centre_pseudo (read : (RingActivePairReport.Slot → List (List Word)) → Option OneCenter.RS) :
    RingFrameTransport.centreG frameZero reader read =
      some ((read (fun k => RingFullPathTrialReadings.trialKey (keys false k) [])).map
        (fun h => (.pseudoasymmetric (pseudoRSOfRS h),.pseudoasymmetric (pseudoRSOfRS h)))) := by
  rw [centre_abstract,letters_rule5]

theorem injective_of_descending (f : RingActivePairReport.Slot → List (List Word))
    (row : List RingActivePairReport.Slot) (perm : row.Perm (List.finRange 4))
    (desc : (row.map f).Pairwise (· > ·)) : Function.Injective f := by
  have nd : (row.map f).Nodup := desc.imp (fun h => ne_of_gt h)
  have rnodup : row.Nodup := perm.nodup_iff.mpr (List.nodup_finRange 4)
  intro a b eq
  exact (List.nodup_map_iff_inj_on rnodup).mp nd a
    (perm.mem_iff.mpr (List.mem_finRange a)) b
    (perm.mem_iff.mpr (List.mem_finRange b)) eq

theorem actual_injective : Function.Injective
    (fun k => RingFullPathTrialReadings.trialKey (keys false k) []) := by
  have eq : trialWord false = fun k => RingFullPathTrialReadings.trialKey (keys false k) [] := funext (trialWord_eq false)
  rw [←eq]
  exact injective_of_descending _ [0,1,2,3] (by decide +kernel) actual_descending

theorem actual_sort : RingStereoSiblingPass.order
    (fun k => RingFullPathTrialReadings.trialKey (keys false k) []) (List.finRange 4) = [0,1,2,3] := by
  have sorted := RingStereoSiblingPass.legal_order (fun k => RingFullPathTrialReadings.trialKey (keys false k) []) (List.finRange 4)
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ ab ba => actual_injective (le_antisymm ba ab))
    (List.pairwise_map.mp sorted.descending) (List.pairwise_map.mp actual_legal.descending)
    (sorted.perm.trans actual_legal.perm.symm)

theorem physical_trial (g : Geometry) :
    RingFrameTransport.readTrialG frameZero g (fun k => RingFullPathTrialReadings.trialKey (keys false k) []) =
      readback? g [1,2,3,4] := by
  unfold RingFrameTransport.readTrialG
  rw [if_pos ((List.nodup_finRange 4).map actual_injective),actual_sort]
  rfl

theorem frame_actual : RingNestedActivePair.frame? reference (origin 0) = some frameZero := by
  rcases frameZero with ⟨c,h,four,ids,read,physical⟩
  simp [RingNestedActivePair.frame?,Option.attach_eq_some _ ⟨c,h⟩,four,
    Option.attach_eq_some _ ⟨ids,read⟩,physical]

theorem publish_pseudo (g : Geometry) :
    RingFrameTransport.publishG reference g (origin 0) reader =
      some ((readback? g [1,2,3,4]).map
        (fun h => (.pseudoasymmetric (pseudoRSOfRS h),.pseudoasymmetric (pseudoRSOfRS h)))) := by
  have notP : RingPyramidalPublication.focusP reference (origin 0) = none := by decide +kernel
  rw [RingFrameTransport.publishG_tetra g notP, RingFrameTransport.tetraG_centre g frame_actual,
    centre_pseudo,physical_trial]

/-! The same reflected evaluator is available for every reader, so remaining
hand/flat cases can share the graph and sorting certificate. -/
namespace Parameterized
def unitWith (rd : Reader reference) : Nat → Arm reference → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← fastBuild (2*((reference.certified.certified.input.molecule.atomCount+1)+1)+1) q
    let labels ← rd q.occurrence
    guard (labels.all RingNestedActivePair.consistent = true ∧ (fastRerootChildren q = [] → labels = none))
    let cs ← (fastRerootChildren q).mapM (unitWith rd n)
    return RingRetainedUnitPass.branch k (RingNestedActivePair.unit (labels.map Prod.fst))
      (KernelSort.sort cs (fun a b => decide (Branch.shallow b ≤ Branch.shallow a)))
      (KernelSort.sort cs (fun a b => decide (Branch.deep b ≤ Branch.deep a)))

theorem unitWith_eq (rd : Reader reference) (n : Nat) (q : Arm reference) : RingRetainedUnitPass.build reference rd n q = unitWith rd n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedUnitPass.build,unitWith,key_eq,rerootChildren_eq,
      RingStereoSiblingPass.order,KernelSort.function_eq]
    have eq : RingRetainedUnitPass.build reference rd n = unitWith rd n := funext ih
    rw [eq]

def refineWith (rd : Reader reference) (prior : Arm reference → Option Branch)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool) : Nat → Arm reference → Option Branch
  | 0,_ => none
  | n+1,q => do
    let p ← prior q
    let v ← rd q.occurrence
    let cs ← (fastRerootChildren q).mapM (refineWith rd prior obs rev n)
    return RingRetainedStereoRefinement.extend p (obs.value v rev)
      (KernelSort.sort cs (fun a b => decide (Branch.shallow b ≤ Branch.shallow a)))
      (KernelSort.sort cs (fun a b => decide (Branch.deep b ≤ Branch.deep a)))

theorem refineWith_eq (rd : Reader reference) (prior : Arm reference → Option Branch)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool) (n : Nat) (q : Arm reference) :
    RingRetainedStereoRefinement.build reference prior rd obs rev n q = refineWith rd prior obs rev n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedStereoRefinement.build,refineWith,rerootChildren_eq,
      RingStereoSiblingPass.order,KernelSort.function_eq]
    have eq : RingRetainedStereoRefinement.build reference prior rd obs rev n = refineWith rd prior obs rev n := funext ih
    rw [eq]

def priorityWith (rd : Reader reference) (rev : Bool) : List RingRetainedStereoRefinement.Observation → Arm reference → Option Branch
  | [],q => unitWith rd (reference.certified.localizedRerootCursorBudget q+1) q
  | o::os,q => refineWith rd (priorityWith rd rev os) o rev (reference.certified.localizedRerootCursorBudget q+1) q

theorem priorityWith_eq (rd : Reader reference) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) :
    RingRetainedStereoRefinement.priority reference rd rev os = priorityWith rd rev os := by
  induction os with
  | nil => funext q; exact unitWith_eq rd _ _
  | cons o os ih =>
    funext q
    simp only [RingRetainedStereoRefinement.priority,priorityWith,ih,refineWith_eq rd]

def nextWith (rd : Reader reference) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : OneCenter.RS)
    (p : RingFullPathPairs.FullVisit reference) : Option (List (RingFullPathPairs.FullVisit reference)) :=
  (fastRerootChildren p.cursor).mapM fun c => do
    let k ← priorityWith rd rev os c
    return ⟨c,p.path ++ [RingFullPathPairs.stepKey k.deep (RingFullPathPairs.likeAt reference rd rev seed c)]⟩

def stageWith (rd : Reader reference) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : OneCenter.RS)
    (q : Arm reference) : Option (List Bool) :=
  (fastSphere RingFullPathPairs.FullVisit.path (nextWith rd rev os seed)
    (reference.certified.localizedRerootCursorBudget q+1) [RingFullPathPairs.rootVisit reference rd rev seed q]).map
    fun out => out.filterMap fun v => RingFullPathPairs.likeAt reference rd rev seed v.cursor

theorem stageWith_eq (rd : Reader reference) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : OneCenter.RS)
    (q : Arm reference) : RingFullPathPairs.stageWords reference rd rev os seed q = stageWith rd rev os seed q := by
  unfold RingFullPathPairs.stageWords RingFullPathPairs.Oracle.bits? RingFullPathPairs.Oracle.visits?
  rw [sphere_eq]
  have nextEq : (RingFullPathPairs.stage reference rd rev os).next?
      (RingFullPathPairs.likeAt reference rd rev seed) = nextWith rd rev os seed := by
    funext p
    simp only [RingFullPathPairs.Oracle.next?,RingFullPathPairs.stage,priorityWith_eq rd,nextWith,rerootChildren_eq]
  rw [nextEq]
  rfl

def keyWith (rd : Reader reference) (rev : Bool) (q : Arm reference) : Option RingFullPathEligibility.Key := do
  let u ← priorityWith rd rev [] q
  let l ← priorityWith rd rev [.lowercase] q
  let ar ← stageWith rd rev [] .R q
  let as' ← stageWith rd rev [] .S q
  let fr ← stageWith rd rev [.lowercase] .R q
  return ⟨u.deep,max ar as',l.word,fr⟩

theorem keyWith_eq (rd : Reader reference) (rev : Bool) (q : Arm reference) :
    RingFullPathEligibility.key? reference rd rev q = keyWith rd rev q := by
  unfold RingFullPathEligibility.key? keyWith RingFullPathPairs.pairs? RingFullPathRule5.word?
  simp only [priorityWith_eq rd,stageWith_eq rd]

assert_kernel_only keyWith_eq
end Parameterized

assert_kernel_only publish_pseudo
assert_kernel_only keys_native
assert_kernel_only actual_legal
assert_kernel_only reflected_legal
assert_kernel_only before5_tie
assert_kernel_only fullKey_eq
assert_kernel_only actual_descending
assert_kernel_only reflected_descending
assert_kernel_only rule5_p1
assert_kernel_only rule5_p2
/-! With exactly one published P hand, Rule 4a already separates the P arms.
Both sides have the same descending order and no Rule 5 reversal. -/
def absentPhosphorusKey : RingFullPathEligibility.Key :=
  { phosphorusKey false with
    throughFourA := (phosphorusKey false).throughFourA.take 3 ++
      [[[0],[0,0],[0,0],[],[],[],[]]]
    bestFourB := []
    fixedR := [] }

def oneFlatReader (h : RS) := canonicalReader (some h) none

def oneFlatKeys (h : RS) (rev : Bool) (k : RingActivePairReport.Slot) : RingFullPathEligibility.Key :=
  ![phosphorusKey ((if rev then h.swap else h) == .R),absentPhosphorusKey,oxygenKey,carbonKey] k

theorem oneFlat_key0 (h : RS) (rev : Bool) :
    Parameterized.keyWith (oneFlatReader h) rev (arm 0) = some (oneFlatKeys h rev 0) := by
  cases h <;> cases rev <;> decide +kernel

theorem oneFlat_key1 (h : RS) (rev : Bool) :
    Parameterized.keyWith (oneFlatReader h) rev (arm 1) = some (oneFlatKeys h rev 1) := by
  cases h <;> cases rev <;> decide +kernel

theorem oneFlat_key2 (h : RS) (rev : Bool) :
    Parameterized.keyWith (oneFlatReader h) rev (arm 2) = some (oneFlatKeys h rev 2) := by
  cases h <;> cases rev <;> decide +kernel

theorem oneFlat_key3 (h : RS) (rev : Bool) :
    Parameterized.keyWith (oneFlatReader h) rev (arm 3) = some (oneFlatKeys h rev 3) := by
  cases h <;> cases rev <;> decide +kernel

theorem oneFlat_key (h : RS) (rev : Bool) (k : RingActivePairReport.Slot) :
    Parameterized.keyWith (oneFlatReader h) rev (arm k) = some (oneFlatKeys h rev k) := by
  fin_cases k
  · exact oneFlat_key0 h rev
  · exact oneFlat_key1 h rev
  · exact oneFlat_key2 h rev
  · exact oneFlat_key3 h rev

theorem oneFlat_native (h : RS) (rev : Bool) :
    RingFullPathPublication.keys? frameZero (oneFlatReader h) rev = some (oneFlatKeys h rev) := by
  have hit (k : RingActivePairReport.Slot) : RingFullPathEligibility.key? reference (oneFlatReader h) rev
      (RingGroupedCentre.cursor frameZero k) = some (oneFlatKeys h rev k) := by
    rw [Parameterized.keyWith_eq,cursor_eq]
    exact oneFlat_key h rev k
  unfold RingFullPathPublication.keys? RingActivePairReport.four?
  simp only [hit,Option.bind_eq_bind,Option.bind_some]
  congr 1

def oneFlatWord (h : RS) (rev : Bool) (k : RingActivePairReport.Slot) :=
  RingFullPathTrialReadings.trialKey (oneFlatKeys h rev k) []

theorem oneFlat_descending (h : RS) (rev : Bool) :
    (([0,1,2,3] : List RingActivePairReport.Slot).map (oneFlatWord h rev)).Pairwise (· > ·) := by
  cases h <;> cases rev <;> decide +kernel

theorem oneFlat_legal (h : RS) (rev : Bool) : RingStereoSiblingPass.Legal
    (oneFlatWord h rev) (List.finRange 4) [0,1,2,3] :=
  ⟨by decide +kernel,(oneFlat_descending h rev).imp (fun gt => le_of_lt gt)⟩

theorem oneFlat_trial (h : RS) : RingFullPathTrialReadings.trials (oneFlatKeys h false) = [none] := by
  cases h <;> decide +kernel

theorem oneFlat_reversals (h : RS) :
    RingFullPathPublication.reversals (oneFlatKeys h false) (oneFlatKeys h true) = 0 := by
  cases h <;> decide +kernel

theorem oneFlat_centre_abstract (h : RS)
    (read : (RingActivePairReport.Slot → List (List Word)) → Option RS) :
    RingFrameTransport.centreG frameZero (oneFlatReader h) read =
      some (RingFullPathPublication.letters (oneFlatKeys h false) (oneFlatKeys h true)
        [read (oneFlatWord h false)]) := by
  unfold RingFrameTransport.centreG RingFrameTransport.readingsG
  change (RingFullPathPublication.keys? frameZero (oneFlatReader h) false).bind _ = _
  rw [oneFlat_native h false]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [oneFlat_native h true]
  simp only [Option.bind_some]
  change ((RingFullPathPublication.keys? frameZero (oneFlatReader h) false).bind _).map _ = _
  rw [oneFlat_native h false]
  simp only [Option.bind_some]
  unfold RingFrameTransport.readingsWithG
  rw [oneFlat_trial]
  simp [RingFullPathTrialReadings.markWords?]
  rfl

theorem oneFlat_letters (h : RS) (focus : Option RS) :
    RingFullPathPublication.letters (oneFlatKeys h false) (oneFlatKeys h true) [focus] =
      focus.map (fun h => (.chiral h,.chiral h.swap)) := by
  unfold RingFullPathPublication.letters
  rw [oneFlat_reversals]
  cases focus with
  | none => rfl
  | some focus => cases focus <;> rfl

theorem oneFlat_sort (h : RS) :
    RingStereoSiblingPass.order (oneFlatWord h false) (List.finRange 4) = [0,1,2,3] := by
  have inj := injective_of_descending (oneFlatWord h false) [0,1,2,3] (by decide +kernel) (oneFlat_descending h false)
  have sorted := RingStereoSiblingPass.legal_order (oneFlatWord h false) (List.finRange 4)
  exact List.Perm.eq_of_pairwise (fun a b _ _ ab ba => inj (le_antisymm ba ab))
    (List.pairwise_map.mp sorted.descending) (List.pairwise_map.mp (oneFlat_legal h false).descending)
    (sorted.perm.trans (oneFlat_legal h false).perm.symm)

theorem oneFlat_physical (h : RS) (g : Geometry) :
    RingFrameTransport.readTrialG frameZero g (oneFlatWord h false) = readback? g [1,2,3,4] := by
  have inj := injective_of_descending (oneFlatWord h false) [0,1,2,3] (by decide +kernel) (oneFlat_descending h false)
  unfold RingFrameTransport.readTrialG
  rw [if_pos ((List.nodup_finRange 4).map inj),oneFlat_sort]
  rfl

theorem oneFlat_publish (h : RS) (g : Geometry) :
    RingFrameTransport.publishG reference g (origin 0) (oneFlatReader h) =
      some ((readback? g [1,2,3,4]).map (fun h => (.chiral h,.chiral h.swap))) := by
  have notP : RingPyramidalPublication.focusP reference (origin 0) = none := by decide +kernel
  rw [RingFrameTransport.publishG_tetra g notP,RingFrameTransport.tetraG_centre g frame_actual,
    oneFlat_centre_abstract,oneFlat_letters,oneFlat_physical]

assert_kernel_only oneFlat_publish
assert_kernel_only oneFlat_key

end TetraStereo.Engine.RingHydrogenSpelling.PhosRootKey
