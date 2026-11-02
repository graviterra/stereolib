import TetraStereo.OneCenter.P93MolecularFullereneNumberedFaceTranscription

set_option autoImplicit false

/-!
# Factored finite certificates for numbered fullerene face maps

The independent fullerene judgments quantify over natural-number atom identifiers.  Concrete
numbered cages must not ask the evaluator to decide those quantified propositions in one large
normalization.  This module reflects only finite lists and exports exact theorems back to the
independent judgments.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler
open TetraStereo.OneCenter.P93CanonicalProgramFullerene

/-! ## Exact finite edge reflection -/

/-- Executable raw-bond-record incidence. -/
def molecularFullereneBonded?
    (molecule : RawMolecule) (left right : Nat) : Bool :=
  molecule.bonds.any fun bond => bond.connects left right

@[simp] theorem molecularFullereneBonded?_eq_true_iff
    (molecule : RawMolecule) (left right : Nat) :
    molecularFullereneBonded? molecule left right = true ↔
      P94ConformationUnit.Bonded molecule left right := by
  simp [molecularFullereneBonded?, P94ConformationUnit.Bonded]

/-- Executable unoriented incidence in one named cyclic face. -/
def molecularFullereneNamedFaceEdge?
    (face : List Nat) (left right : Nat) : Bool :=
  isForwardMolecularFullereneFaceEdge face left right ||
    isForwardMolecularFullereneFaceEdge face right left

/-- Exact reflection of `IsNamedCycleEdge` for the duplicate-free faces admitted below. -/
theorem molecularFullereneNamedFaceEdge?_eq_true_iff
    (face : List Nat) (faceNodup : face.Nodup) (left right : Nat) :
    molecularFullereneNamedFaceEdge? face left right = true ↔
      IsNamedCycleEdge face left right := by
  rw [molecularFullereneNamedFaceEdge?, Bool.or_eq_true,
    isForwardMolecularFullereneFaceEdge_eq_true_iff,
    isForwardMolecularFullereneFaceEdge_eq_true_iff]
  constructor
  · rintro (forward | reverse)
    · exact ⟨forward.1, Or.inl forward.2⟩
    · refine ⟨reverse.2 ▸ List.next_mem face right reverse.1, Or.inr ?_⟩
      simpa only [reverse.2] using List.prev_next face faceNodup right reverse.1
  · rintro ⟨leftPresent, next | previous⟩
    · exact Or.inl ⟨leftPresent, next⟩
    · right
      have rightPresent : right ∈ face := previous ▸ List.prev_mem face left leftPresent
      refine ⟨rightPresent, ?_⟩
      simpa only [← previous] using List.next_prev face faceNodup left leftPresent

/-! ## Finite independent-face admission -/

/-- Finite reflection of consecutive raw-bond-record incidence. -/
def molecularFullereneConsecutivelyBonded?
    (molecule : RawMolecule) (atoms : List Nat) : Bool :=
  (atoms.zip atoms.tail).all fun edge =>
    molecularFullereneBonded? molecule edge.1 edge.2

@[simp] theorem molecularFullereneConsecutivelyBonded?_eq_true_iff
    (molecule : RawMolecule) (atoms : List Nat) :
    molecularFullereneConsecutivelyBonded? molecule atoms = true ↔
      P94ConformationUnit.ConsecutivelyBonded molecule atoms := by
  simp [molecularFullereneConsecutivelyBonded?,
    P94ConformationUnit.ConsecutivelyBonded, List.all_eq_true]

/-- Finite reflection of raw closing plus consecutive bond records. -/
def molecularFullereneCyclicallyBonded?
    (molecule : RawMolecule) (atoms : List Nat) : Bool :=
  molecularFullereneConsecutivelyBonded? molecule atoms &&
    match atoms.head?, atoms.reverse.head? with
    | some first, some last => molecularFullereneBonded? molecule last first
    | _, _ => false

@[simp] theorem molecularFullereneCyclicallyBonded?_eq_true_iff
    (molecule : RawMolecule) (atoms : List Nat) :
    molecularFullereneCyclicallyBonded? molecule atoms = true ↔
      P94ConformationUnit.CyclicallyBonded molecule atoms := by
  simp only [molecularFullereneCyclicallyBonded?, Bool.and_eq_true,
    molecularFullereneConsecutivelyBonded?_eq_true_iff]
  constructor
  · rintro ⟨consecutive, closing⟩
    refine ⟨consecutive, ?_⟩
    cases firstEq : atoms.head? with
    | none => simp [firstEq] at closing
    | some first =>
        cases lastEq : atoms.reverse.head? with
        | none => simp [firstEq, lastEq] at closing
        | some last =>
            simp only [firstEq, lastEq] at closing
            exact ⟨first, last, rfl, rfl,
              (molecularFullereneBonded?_eq_true_iff _ _ _).mp closing⟩
  · rintro ⟨consecutive, first, last, firstEq, lastEq, closing⟩
    refine ⟨consecutive, ?_⟩
    simp only [firstEq, lastEq]
    exact (molecularFullereneBonded?_eq_true_iff _ _ _).mpr closing

/-- The kind-independent ring carrier used by `IndependentP94RingTraversal`. -/
def molecularFullereneTraversalUnit (atoms : List Nat) : P94ConformationUnit :=
  { kind := .fiveMemberedRing, atoms := atoms }


def molecularFullereneInducedFace?
    (molecule : RawMolecule) (atoms : List Nat) : Bool :=
  atoms.all fun left => atoms.all fun right =>
    if left = right then true
    else molecularFullereneBonded? molecule left right ==
      molecularFullereneNamedFaceEdge? atoms left right

theorem molecularFullereneInducedFace?_eq_true_iff
    (molecule : RawMolecule) (atoms : List Nat) (atomsNodup : atoms.Nodup) :
    molecularFullereneInducedFace? molecule atoms = true ↔
      ∀ left ∈ atoms, ∀ right ∈ atoms, left ≠ right →
        (P94ConformationUnit.Bonded molecule left right ↔
          IsNamedCycleEdge atoms left right) := by
  simp only [molecularFullereneInducedFace?, List.all_eq_true]
  constructor
  · intro checked left leftPresent right rightPresent distinct
    have localCheck := checked left leftPresent right rightPresent
    have boolEq : molecularFullereneBonded? molecule left right =
        molecularFullereneNamedFaceEdge? atoms left right := by
      simpa only [if_neg distinct, beq_iff_eq] using localCheck
    constructor
    · intro bonded
      have bondedTrue :=
        (molecularFullereneBonded?_eq_true_iff molecule left right).mpr bonded
      apply (molecularFullereneNamedFaceEdge?_eq_true_iff atoms atomsNodup left right).mp
      exact boolEq.symm.trans bondedTrue
    · intro named
      have namedTrue :=
        (molecularFullereneNamedFaceEdge?_eq_true_iff atoms atomsNodup left right).mpr named
      apply (molecularFullereneBonded?_eq_true_iff molecule left right).mp
      exact boolEq.trans namedTrue
  · intro judged left leftPresent right rightPresent
    by_cases distinct : left = right
    · simp [distinct]
    · simp only [if_neg distinct, beq_iff_eq]
      apply Bool.eq_iff_iff.mpr
      rw [molecularFullereneBonded?_eq_true_iff,
        molecularFullereneNamedFaceEdge?_eq_true_iff atoms atomsNodup]
      exact judged left leftPresent right rightPresent distinct

/-- Complete finite checker for the pre-existing independent traversal judgment. -/
def independentP94RingTraversalAccepted
    (molecule : RawMolecule) (atoms : List Nat) : Bool :=
  decide (3 ≤ atoms.length) &&
    decide atoms.Nodup &&
    atoms.all (fun atom => decide (atom < molecule.atomCount)) &&
    molecularFullereneCyclicallyBonded? molecule atoms &&
    (molecularFullereneTraversalUnit atoms).cycleCarrier? molecule &&
    molecularFullereneInducedFace? molecule atoms

/-- The finite checker is extensionally exact for the independent molecular traversal
judgment.  In particular, evaluating it never ranges over atoms outside the supplied face. -/
@[simp] theorem independentP94RingTraversalAccepted_eq_true_iff
    (molecule : RawMolecule) (atoms : List Nat) :
    independentP94RingTraversalAccepted molecule atoms = true ↔
      IndependentP94RingTraversal molecule atoms := by
  simp only [independentP94RingTraversalAccepted, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨minimum, nodup, bounded, cyclicAccepted, carrierAccepted, inducedAccepted⟩
    refine ⟨minimum, nodup, bounded,
      (molecularFullereneCyclicallyBonded?_eq_true_iff molecule atoms).mp cyclicAccepted,
      ?_, (molecularFullereneInducedFace?_eq_true_iff molecule atoms nodup).mp
        inducedAccepted⟩
    have carrier :=
      (P94ConformationUnit.cycleCarrier?_eq_true_iff
        (molecularFullereneTraversalUnit atoms) molecule).mp carrierAccepted
    simpa [molecularFullereneTraversalUnit] using carrier
  · rintro ⟨minimum, nodup, bounded, cyclic, carrier, induced⟩
    refine ⟨minimum, nodup, bounded,
      (molecularFullereneCyclicallyBonded?_eq_true_iff molecule atoms).mpr cyclic,
      ?_, (molecularFullereneInducedFace?_eq_true_iff molecule atoms nodup).mpr induced⟩
    apply (P94ConformationUnit.cycleCarrier?_eq_true_iff
      (molecularFullereneTraversalUnit atoms) molecule).mpr
    simpa [molecularFullereneTraversalUnit] using carrier

/-! ## Checked explicit connectivity routes -/

/-- Finite checker for one explicit simple carrier route. -/
def molecularFullerenePackagePathAccepted
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (first second : Nat) (path : List Nat) : Bool :=
  decide path.Nodup &&
    path.all (fun atom => decide (atom ∈ package.carrier)) &&
    decide (path.head? = some first) &&
    decide (path.getLast? = some second) &&
    molecularFullereneConsecutivelyBonded? molecule path

@[simp] theorem molecularFullerenePackagePathAccepted_eq_true_iff
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (first second : Nat) (path : List Nat) :
    molecularFullerenePackagePathAccepted molecule package first second path = true ↔
      MolecularFullereneCagePath molecule package.carrier first second path := by
  simp only [molecularFullerenePackagePathAccepted, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true,
    molecularFullereneConsecutivelyBonded?_eq_true_iff, and_assoc,
    MolecularFullereneCagePath]

/-- A route function is evaluated only on pairs from the finite source-locant list. -/
structure MolecularFullereneExplicitRoutes where
  route : Nat → Nat → List Nat

/-- Check every ordered carrier pair against its explicit route. -/
def molecularFullereneAllRoutesAccepted
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (routes : MolecularFullereneExplicitRoutes) : Bool :=
  package.atomsByLocant.all fun first =>
    package.atomsByLocant.all fun second =>
      molecularFullerenePackagePathAccepted molecule package first second
        (routes.route first second)

/-- Finite checked routes prove the original quantified connectedness judgment. -/
theorem molecularFullereneCageConnected_of_allRoutesAccepted
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (routes : MolecularFullereneExplicitRoutes)
    (atomsNonempty : package.atomsByLocant ≠ [])
    (accepted : molecularFullereneAllRoutesAccepted molecule package routes = true) :
    MolecularFullereneCageConnected molecule package.carrier := by
  refine ⟨?_, ?_⟩
  · rw [MolecularFullereneNumberedCagePackage.carrier, Finset.nonempty_iff_ne_empty]
    simpa using atomsNonempty
  · intro first firstPresent second secondPresent
    have firstListed : first ∈ package.atomsByLocant := by
      simpa [MolecularFullereneNumberedCagePackage.carrier] using firstPresent
    have secondListed : second ∈ package.atomsByLocant := by
      simpa [MolecularFullereneNumberedCagePackage.carrier] using secondPresent
    have allFirst := (List.all_eq_true.mp accepted) first firstListed
    have routeAccepted := (List.all_eq_true.mp allFirst) second secondListed
    exact ⟨routes.route first second,
      (molecularFullerenePackagePathAccepted_eq_true_iff molecule package first second
        (routes.route first second)).mp routeAccepted⟩

/-! ## Linear Hamiltonian connectivity -/

theorem consecutivelyBonded_iff_isChain
    (molecule : RawMolecule) (atoms : List Nat) :
    P94ConformationUnit.ConsecutivelyBonded molecule atoms ↔
      atoms.IsChain (P94ConformationUnit.Bonded molecule) := by
  induction atoms with
  | nil => simp [P94ConformationUnit.ConsecutivelyBonded]
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil => simp [P94ConformationUnit.ConsecutivelyBonded]
      | cons second rest =>
          constructor
          · intro bonded
            apply List.IsChain.cons_cons
            · exact bonded (first, second) (by simp)
            · apply inductionHypothesis.mp
              intro edge edgePresent
              apply bonded edge
              simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
              exact Or.inr edgePresent
          · intro chain edge edgePresent
            rcases (List.isChain_cons_cons.mp chain) with ⟨firstBond, tailChain⟩
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at edgePresent
            rcases edgePresent with rfl | edgePresent
            · exact firstBond
            · exact (inductionHypothesis.mpr tailChain) edge edgePresent

theorem p94Bonded_symm (molecule : RawMolecule) (left right : Nat) :
    P94ConformationUnit.Bonded molecule left right ↔
      P94ConformationUnit.Bonded molecule right left := by
  simp only [P94ConformationUnit.Bonded]
  constructor <;> rintro ⟨bond, present, connected⟩ <;>
    refine ⟨bond, present, ?_⟩ <;>
    simpa [RawBond.connects, Bool.or_comm] using connected

@[simp] private theorem range'_head?_succ (start length : Nat) :
    (List.range' start (length + 1)).head? = some start := by
  cases length <;> rfl

@[simp] private theorem range'_getLast?_succ (start length : Nat) :
    (List.range' start (length + 1)).getLast? = some (start + length) := by
  rw [List.getLast?_eq_getElem?]
  simp

/-- Systematic locants form a Hamiltonian path in each numbered P-93 fullerene cage.  Checking
the `N-1` consecutive bonds is therefore sufficient for quantified carrier connectedness; the
proof constructs the appropriate ascending or reversed interval for every pair without
evaluating an all-pairs route table. -/
theorem molecularFullereneCageConnected_of_range_hamiltonian
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (atomCount : Nat)
    (atomsExact : package.atomsByLocant = List.range atomCount)
    (consecutive : ∀ atom, atom + 1 < atomCount →
      P94ConformationUnit.Bonded molecule atom (atom + 1))
    (positiveCount : 0 < atomCount) :
    MolecularFullereneCageConnected molecule package.carrier := by
  have carrierExact : package.carrier = Finset.range atomCount := by
    ext atom
    simp [MolecularFullereneNumberedCagePackage.carrier, atomsExact]
  constructor
  · rw [carrierExact]
    exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt positiveCount)
  · intro first firstPresent second secondPresent
    have firstBound : first < atomCount := by simpa [carrierExact] using firstPresent
    have secondBound : second < atomCount := by simpa [carrierExact] using secondPresent
    by_cases ordered : first ≤ second
    · let path := List.range' first (second - first + 1)
      refine ⟨path, ?_, ?_, ?_, ?_, ?_⟩
      · exact List.nodup_range'
      · intro atom atomPresent
        rw [carrierExact, Finset.mem_range]
        rcases List.mem_range'.mp atomPresent with ⟨index, indexBound, rfl⟩
        omega
      · simp [path]
      · simp [path, Nat.add_sub_of_le ordered]
      · rw [consecutivelyBonded_iff_isChain]
        apply (List.isChain_range' first (second - first + 1) 1).imp_of_mem_imp
        intro left right _leftPresent rightPresent rightEq
        subst right
        apply consecutive left
        rcases List.mem_range'.mp rightPresent with ⟨index, indexBound, rightEq⟩
        have endpoint : first + (second - first) = second := Nat.add_sub_of_le ordered
        omega
    · have reverseOrdered : second ≤ first := Nat.le_of_lt (Nat.lt_of_not_ge ordered)
      let forward := List.range' second (first - second + 1)
      let path := forward.reverse
      refine ⟨path, ?_, ?_, ?_, ?_, ?_⟩
      · exact List.nodup_reverse.mpr List.nodup_range'
      · intro atom atomPresent
        rw [carrierExact, Finset.mem_range]
        have forwardPresent : atom ∈ forward := by simpa [path] using atomPresent
        rcases List.mem_range'.mp forwardPresent with ⟨index, indexBound, rfl⟩
        omega
      · simp [path, forward, Nat.add_sub_of_le reverseOrdered]
      · simp [path, forward]
      · rw [consecutivelyBonded_iff_isChain]
        change forward.reverse.IsChain (P94ConformationUnit.Bonded molecule)
        rw [List.isChain_reverse]
        apply (List.isChain_range' second (first - second + 1) 1).imp_of_mem_imp
        intro left right _leftPresent rightPresent rightEq
        subst right
        exact (p94Bonded_symm molecule left (left + 1)).mp
          (consecutive left (by
            rcases List.mem_range'.mp rightPresent with ⟨index, indexBound, rightEq⟩
            have endpoint : second + (first - second) = first :=
              Nat.add_sub_of_le reverseOrdered
            omega))

/-! ## Face-derived cage table -/

theorem numberedFaceTranscription_mem_edgeTable_iff
    (transcription : NumberedFaceTranscription) (left right : Nat) :
    (left, right) ∈ transcription.edgeTable ↔
      left < transcription.atomCount ∧ right < transcription.atomCount ∧
        left < right ∧ transcription.hasFaceEdge left right = true := by
  simp [NumberedFaceTranscription.edgeTable]

/-- The row-by-row range enumeration used by `edgeTable` is duplicate-free for every
transcription; this is structural and does not inspect any concrete face data. -/
theorem numberedFaceTranscription_edgeTable_nodup
    (transcription : NumberedFaceTranscription) : transcription.edgeTable.Nodup := by
  rw [NumberedFaceTranscription.edgeTable, List.nodup_flatMap]
  refine ⟨?_, List.nodup_range.imp ?_⟩
  · intro left _leftPresent
    exact (List.nodup_range.filter _).map (fun right₁ right₂ equal =>
      (Prod.mk.inj equal).2)
  · intro left₁ left₂ different
    rw [Function.onFun, List.disjoint_left]
    intro edge firstPresent secondPresent
    rcases List.mem_map.mp firstPresent with ⟨right₁, _right₁Present, firstEq⟩
    rcases List.mem_map.mp secondPresent with ⟨right₂, _right₂Present, secondEq⟩
    exact different (congrArg Prod.fst (firstEq.trans secondEq.symm))

theorem numberedFaceTranscription_hasFaceEdge_symm
    (transcription : NumberedFaceTranscription) (left right : Nat) :
    transcription.hasFaceEdge left right = transcription.hasFaceEdge right left := by
  simp [NumberedFaceTranscription.hasFaceEdge, Bool.or_comm]

/-- Exact structural graph boundary for a generated cage: bounded distinct atoms have a raw bond
record exactly when the source face transcription contains their undirected edge.  This theorem
unfolds the mapped edge list once in the proof and eliminates all later molecular bond scans. -/
theorem numberedFaceTranscription_bonded_iff_hasFaceEdge
    (transcription : NumberedFaceTranscription) (left right : Nat)
    (leftBound : left < transcription.atomCount)
    (rightBound : right < transcription.atomCount) (distinct : left ≠ right) :
    P94ConformationUnit.Bonded transcription.cageMolecule left right ↔
      transcription.hasFaceEdge left right = true := by
  constructor
  · rintro ⟨bond, bondPresent, connects⟩
    change bond ∈ transcription.edgeTable.map NumberedFaceTranscription.singleBond at bondPresent
    rcases List.mem_map.mp bondPresent with ⟨edge, edgePresent, rfl⟩
    have edgeData := (numberedFaceTranscription_mem_edgeTable_iff
      transcription edge.1 edge.2).mp edgePresent
    simp only [NumberedFaceTranscription.singleBond, RawBond.connects,
      Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
    rcases connects with forward | reverse
    · have edgeEq : edge = (left, right) := by
        apply Prod.ext
        · simpa using forward.1
        · simpa using forward.2
      subst edge
      exact edgeData.2.2.2
    · have edgeEq : edge = (right, left) := by
        apply Prod.ext
        · simpa using reverse.1
        · simpa using reverse.2
      subst edge
      rw [numberedFaceTranscription_hasFaceEdge_symm]
      exact edgeData.2.2.2
  · intro faceEdge
    rcases lt_or_gt_of_ne distinct with ordered | ordered
    · have edgePresent : (left, right) ∈ transcription.edgeTable :=
        (numberedFaceTranscription_mem_edgeTable_iff transcription left right).mpr
          ⟨leftBound, rightBound, ordered, faceEdge⟩
      refine ⟨NumberedFaceTranscription.singleBond (left, right), ?_, ?_⟩
      · change NumberedFaceTranscription.singleBond (left, right) ∈
          transcription.edgeTable.map NumberedFaceTranscription.singleBond
        exact List.mem_map.mpr ⟨(left, right), edgePresent, rfl⟩
      · simp [NumberedFaceTranscription.singleBond, RawBond.connects]
    · have reverseFaceEdge : transcription.hasFaceEdge right left = true := by
        rw [numberedFaceTranscription_hasFaceEdge_symm]
        exact faceEdge
      have edgePresent : (right, left) ∈ transcription.edgeTable :=
        (numberedFaceTranscription_mem_edgeTable_iff transcription right left).mpr
          ⟨rightBound, leftBound, ordered, reverseFaceEdge⟩
      refine ⟨NumberedFaceTranscription.singleBond (right, left), ?_, ?_⟩
      · change NumberedFaceTranscription.singleBond (right, left) ∈
          transcription.edgeTable.map NumberedFaceTranscription.singleBond
        exact List.mem_map.mpr ⟨(right, left), edgePresent, rfl⟩
      · simp [NumberedFaceTranscription.singleBond, RawBond.connects]

/-- Carrier-bounded face adjacency, excluding the atom itself. -/
def numberedFaceTranscriptionFaceNeighbors
    (transcription : NumberedFaceTranscription) (atom : Nat) : Finset Nat :=
  (Finset.range transcription.atomCount).filter fun neighbor =>
    neighbor ≠ atom ∧ transcription.hasFaceEdge atom neighbor = true

/-- The molecular neighbors of a generated cage are exactly its source-face neighbors.  This is
an extensional semantic transport through the exact raw-bond theorem, not a bond-order
normalization. -/
theorem numberedFaceTranscription_cageNeighbors_eq_faceNeighbors
    (transcription : NumberedFaceTranscription) (atom : Nat)
    (atomBound : atom < transcription.atomCount) :
    molecularFullereneCageNeighbors transcription.cageMolecule
        transcription.numberedPackage.carrier atom =
      numberedFaceTranscriptionFaceNeighbors transcription atom := by
  ext neighbor
  simp only [molecularFullereneCageNeighbors, Finset.mem_filter,
    MolecularFullereneNumberedCagePackage.carrier,
    NumberedFaceTranscription.numberedPackage,
    NumberedFaceTranscription.atomsByLocant, List.mem_toFinset, List.mem_range,
    numberedFaceTranscriptionFaceNeighbors, Finset.mem_range]
  constructor
  · rintro ⟨neighborBound, positive⟩
    have distinct : atom ≠ neighbor := by
      intro equal
      subst neighbor
      simp [RawMolecule.bondOrder_self] at positive
    have bonded := (transcription.cageMolecule.bondOrder_pos_iff_exists_bond distinct).mp positive
    exact ⟨neighborBound, Ne.symm distinct,
      (numberedFaceTranscription_bonded_iff_hasFaceEdge transcription atom neighbor
        atomBound neighborBound distinct).mp bonded⟩
  · rintro ⟨neighborBound, neighborDistinct, faceEdge⟩
    have distinct : atom ≠ neighbor := Ne.symm neighborDistinct
    refine ⟨neighborBound,
      (transcription.cageMolecule.bondOrder_pos_iff_exists_bond distinct).mpr ?_⟩
    exact (numberedFaceTranscription_bonded_iff_hasFaceEdge transcription atom neighbor
      atomBound neighborBound distinct).mpr faceEdge

private theorem zip_tail_append_singleton
    {Alpha : Type*} (first closing : Alpha) : ∀ rest : List Alpha,
    (first :: rest).zip (rest ++ [closing]) =
      (first :: rest).zip rest ++ [((first :: rest).getLast (by simp), closing)]
  | [] => by simp
  | second :: rest => by
      simp only [List.zip_cons_cons, List.cons_append]
      rw [zip_tail_append_singleton second closing rest]
      rfl

private theorem getLast?_getD_eq_getLast_cons
    {Alpha : Type*} (first : Alpha) : ∀ rest : List Alpha,
    rest.getLast?.getD first = (first :: rest).getLast (by simp)
  | [] => rfl
  | second :: rest => by
      rw [List.getLast_cons (by simp)]
      rw [List.getLast?_eq_getLast_of_ne_nil (l := second :: rest) (by simp)]
      rfl

private theorem nodup_zip_tail_distinct {Alpha : Type*}
    [DecidableEq Alpha] (atoms : List Alpha) (nodup : atoms.Nodup) :
    ∀ edge ∈ atoms.zip atoms.tail, edge.1 ≠ edge.2 := by
  induction atoms with
  | nil => simp
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => simp
      | cons second tail =>
          have nodupParts := List.nodup_cons.mp nodup
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
          intro edge present
          rcases present with rfl | present
          · exact fun equal => nodupParts.1 (by
              rw [List.mem_cons]
              exact Or.inl equal)
          · exact inductionHypothesis nodupParts.2 edge present

/-- A duplicate-free molecular cyclic traversal already contains exactly the positive closing
and path bond orders required by `CycleCarrier`.  This is a semantic theorem: it decomposes the
closed edge list and never evaluates `cycleCarrier?` or a molecular bond-order table. -/
theorem cycleCarrier_of_cyclicallyBonded
    (molecule : RawMolecule) (atoms : List Nat)
    (minimum : 3 ≤ atoms.length) (nodup : atoms.Nodup)
    (bounded : ∀ atom ∈ atoms, atom < molecule.atomCount)
    (cyclic : P94ConformationUnit.CyclicallyBonded molecule atoms) :
    (molecularFullereneTraversalUnit atoms).CycleCarrier molecule := by
  rcases cyclic with ⟨consecutive, first, last, firstEq, lastEq, closing⟩
  rcases List.head?_eq_some_iff.mp firstEq with ⟨rest, rfl⟩
  have restNonempty : rest ≠ [] := by
    intro restEmpty
    subst rest
    simp at minimum
  have lastEq' : rest.getLast restNonempty = last := by
    simpa [List.getLast?_eq_some_getLast restNonempty] using lastEq
  have nodupParts := List.nodup_cons.mp nodup
  refine ⟨minimum, nodup, bounded, ?_⟩
  intro edge edgePresent
  change edge ∈ P94ConformationUnit.cyclicAdjacentPairs (first :: rest) at edgePresent
  rw [P94ConformationUnit.cyclicAdjacentPairs_cons,
    zip_tail_append_singleton first first rest] at edgePresent
  rw [List.mem_append, List.mem_singleton] at edgePresent
  have edgeDistinct : edge.1 ≠ edge.2 := by
    rcases edgePresent with pathEdge | closingEdge
    · exact nodup_zip_tail_distinct (first :: rest) nodup edge pathEdge
    · subst edge
      exact fun equal => nodupParts.1 (by
        simp only at equal
        rw [List.getLast_cons restNonempty, lastEq'] at equal
        rw [← equal, ← lastEq']
        exact List.getLast_mem restNonempty)
  apply (molecule.bondOrder_pos_iff_exists_bond edgeDistinct).mpr
  rcases edgePresent with pathEdge | closingEdge
  · exact consecutive edge pathEdge
  · subst edge
    simpa [List.getLast_cons restNonempty, lastEq'] using closing

/-- Distinct vertices in a duplicate-free traversal give distinct endpoints to every closed
cycle edge, including the final-to-first edge. -/
theorem cycleEdges_distinct_of_minimum_nodup
    (atoms : List Nat) (minimum : 3 ≤ atoms.length) (nodup : atoms.Nodup) :
    ∀ edge ∈ (molecularFullereneTraversalUnit atoms).cycleEdges,
      edge.1 ≠ edge.2 := by
  cases atoms with
  | nil => simp at minimum
  | cons first rest =>
      have restNonempty : rest ≠ [] := by
        intro restEmpty
        subst rest
        simp at minimum
      have nodupParts := List.nodup_cons.mp nodup
      intro edge edgePresent
      change edge ∈ P94ConformationUnit.cyclicAdjacentPairs (first :: rest) at edgePresent
      rw [P94ConformationUnit.cyclicAdjacentPairs_cons,
        zip_tail_append_singleton first first rest] at edgePresent
      rw [List.mem_append, List.mem_singleton] at edgePresent
      rcases edgePresent with pathEdge | closingEdge
      · exact nodup_zip_tail_distinct (first :: rest) nodup edge pathEdge
      · subst edge
        exact fun equal => nodupParts.1 (by
          simp only at equal
          rw [List.getLast_cons restNonempty] at equal
          rw [← equal]
          exact List.getLast_mem restNonempty)

/-- Bonding every explicitly enumerated closed edge proves the raw cyclic traversal predicate. -/
theorem cyclicallyBonded_of_cycleEdges_bonded
    (molecule : RawMolecule) (atoms : List Nat) (minimum : 3 ≤ atoms.length)
    (edgesBonded : ∀ edge ∈ (molecularFullereneTraversalUnit atoms).cycleEdges,
      P94ConformationUnit.Bonded molecule edge.1 edge.2) :
    P94ConformationUnit.CyclicallyBonded molecule atoms := by
  cases atoms with
  | nil => simp at minimum
  | cons first rest =>
      refine ⟨?_, first, (first :: rest).getLast (by simp), rfl, ?_, ?_⟩
      · intro edge edgePresent
        apply edgesBonded edge
        change edge ∈ P94ConformationUnit.cyclicAdjacentPairs (first :: rest)
        rw [P94ConformationUnit.cyclicAdjacentPairs_cons,
          zip_tail_append_singleton first first rest, List.mem_append]
        exact Or.inl edgePresent
      · simpa using getLast?_getD_eq_getLast_cons first rest
      · apply edgesBonded ((first :: rest).getLast (by simp), first)
        change ((first :: rest).getLast (by simp), first) ∈
          P94ConformationUnit.cyclicAdjacentPairs (first :: rest)
        rw [P94ConformationUnit.cyclicAdjacentPairs_cons,
          zip_tail_append_singleton first first rest]
        simp

/-- Complete semantic constructor from a source face's own closed edge ledger.  Source clients
need only prove that each listed closed edge occurs in the face-derived graph and that the face is
induced; cyclic bonding and the normalized molecular carrier are mathematical consequences. -/
theorem independentP94RingTraversal_of_sourceFaceEdges
    (transcription : NumberedFaceTranscription) (face : List Nat)
    (minimum : 3 ≤ face.length) (nodup : face.Nodup)
    (bounded : ∀ atom ∈ face, atom < transcription.atomCount)
    (sourceCycleEdges : ∀ edge ∈ (molecularFullereneTraversalUnit face).cycleEdges,
      transcription.hasFaceEdge edge.1 edge.2 = true)
    (sourceInduced : ∀ left ∈ face, ∀ right ∈ face, left ≠ right →
      (transcription.hasFaceEdge left right = true ↔ IsNamedCycleEdge face left right)) :
    IndependentP94RingTraversal transcription.cageMolecule face := by
  have edgeDistinct := cycleEdges_distinct_of_minimum_nodup face minimum nodup
  have edgesBonded : ∀ edge ∈ (molecularFullereneTraversalUnit face).cycleEdges,
      P94ConformationUnit.Bonded transcription.cageMolecule edge.1 edge.2 := by
    intro edge edgePresent
    have zippedPresent : edge ∈ face.zip (face.tail ++ face.take 1) := by
      simpa [molecularFullereneTraversalUnit, P94ConformationUnit.cycleEdges,
        P94ConformationUnit.cyclicAdjacentPairs, P94ConformationUnit.cyclicSuccessors] using
          edgePresent
    have leftPresent : edge.1 ∈ face := (List.of_mem_zip zippedPresent).1
    have rightSuccessor : edge.2 ∈ face.tail ++ face.take 1 :=
      (List.of_mem_zip zippedPresent).2
    have rightPresent : edge.2 ∈ face := by
      rcases List.mem_append.mp rightSuccessor with tailPresent | headPresent
      · exact List.mem_of_mem_tail tailPresent
      · exact List.mem_of_mem_take headPresent
    exact (numberedFaceTranscription_bonded_iff_hasFaceEdge transcription edge.1 edge.2
      (bounded edge.1 leftPresent) (bounded edge.2 rightPresent)
      (edgeDistinct edge edgePresent)).mpr (sourceCycleEdges edge edgePresent)
  have boundedMolecule : ∀ atom ∈ face, atom < transcription.cageMolecule.atomCount := by
    intro atom present
    simpa [NumberedFaceTranscription.cageMolecule, RawMolecule.atomCount] using
      bounded atom present
  have cyclic := cyclicallyBonded_of_cycleEdges_bonded
    transcription.cageMolecule face minimum edgesBonded
  refine ⟨minimum, nodup, boundedMolecule, cyclic, ?_, ?_⟩
  · simpa [molecularFullereneTraversalUnit] using
      cycleCarrier_of_cyclicallyBonded transcription.cageMolecule face minimum nodup
        boundedMolecule cyclic
  · intro left leftPresent right rightPresent distinct
    exact (numberedFaceTranscription_bonded_iff_hasFaceEdge transcription left right
      (bounded left leftPresent) (bounded right rightPresent) distinct).trans
        (sourceInduced left leftPresent right rightPresent distinct)

/-- Executable independent-face acceptance obtained from the fully semantic source-edge
constructor, without evaluating either the cyclic or cycle-carrier molecular checker. -/
theorem independentP94RingTraversalAccepted_of_sourceFaceEdges
    (transcription : NumberedFaceTranscription) (face : List Nat)
    (minimum : 3 ≤ face.length) (nodup : face.Nodup)
    (bounded : ∀ atom ∈ face, atom < transcription.atomCount)
    (sourceCycleEdges : ∀ edge ∈ (molecularFullereneTraversalUnit face).cycleEdges,
      transcription.hasFaceEdge edge.1 edge.2 = true)
    (sourceInduced : ∀ left ∈ face, ∀ right ∈ face, left ≠ right →
      (transcription.hasFaceEdge left right = true ↔ IsNamedCycleEdge face left right)) :
    independentP94RingTraversalAccepted transcription.cageMolecule face = true :=
  (independentP94RingTraversalAccepted_eq_true_iff transcription.cageMolecule face).mpr
    (independentP94RingTraversal_of_sourceFaceEdges transcription face minimum nodup bounded
      sourceCycleEdges sourceInduced)

/-- Semantic source-face constructor.  The induced-graph clause is transported through the exact
structural bond theorem, while the normalized cycle carrier follows mathematically from the raw
cyclic traversal.  No molecular checker is evaluated inside this theorem. -/
theorem independentP94RingTraversal_of_sourceFace
    (transcription : NumberedFaceTranscription) (face : List Nat)
    (minimum : 3 ≤ face.length) (nodup : face.Nodup)
    (bounded : ∀ atom ∈ face, atom < transcription.atomCount)
    (cyclic : P94ConformationUnit.CyclicallyBonded transcription.cageMolecule face)
    (sourceInduced : ∀ left ∈ face, ∀ right ∈ face, left ≠ right →
      (transcription.hasFaceEdge left right = true ↔ IsNamedCycleEdge face left right)) :
    IndependentP94RingTraversal transcription.cageMolecule face := by
  have boundedMolecule : ∀ atom ∈ face, atom < transcription.cageMolecule.atomCount := by
    intro atom present
    simpa [NumberedFaceTranscription.cageMolecule, RawMolecule.atomCount] using
      bounded atom present
  refine ⟨minimum, nodup, boundedMolecule, cyclic, ?_, ?_⟩
  · simpa [molecularFullereneTraversalUnit] using
      cycleCarrier_of_cyclicallyBonded transcription.cageMolecule face minimum nodup
        boundedMolecule cyclic
  · intro left leftPresent right rightPresent distinct
    exact (numberedFaceTranscription_bonded_iff_hasFaceEdge transcription left right
      (bounded left leftPresent) (bounded right rightPresent) distinct).trans
        (sourceInduced left leftPresent right rightPresent distinct)

/-- Executable face acceptance follows from the semantic source constructor without evaluating
the molecule-bound checker. -/
theorem independentP94RingTraversalAccepted_of_sourceFace
    (transcription : NumberedFaceTranscription) (face : List Nat)
    (minimum : 3 ≤ face.length) (nodup : face.Nodup)
    (bounded : ∀ atom ∈ face, atom < transcription.atomCount)
    (cyclic : P94ConformationUnit.CyclicallyBonded transcription.cageMolecule face)
    (sourceInduced : ∀ left ∈ face, ∀ right ∈ face, left ≠ right →
      (transcription.hasFaceEdge left right = true ↔ IsNamedCycleEdge face left right)) :
    independentP94RingTraversalAccepted transcription.cageMolecule face = true :=
  (independentP94RingTraversalAccepted_eq_true_iff transcription.cageMolecule face).mpr
    (independentP94RingTraversal_of_sourceFace transcription face minimum nodup bounded cyclic
      sourceInduced)


structure FaceDerivedTableAudit (transcription : NumberedFaceTranscription) : Prop where
  edgeTableNodup : transcription.edgeTable.Nodup


def FaceDerivedTableAudit.canonical (transcription : NumberedFaceTranscription) :
    FaceDerivedTableAudit transcription where
  edgeTableNodup := numberedFaceTranscription_edgeTable_nodup transcription

/-- The molecule generated from one face-derived edge table satisfies the complete independent
numbered-table judgment.  The molecular equality is proved structurally from the mapped bond
records, not by evaluating a quadratic `Finset` equality. -/
theorem FaceDerivedTableAudit.tableJudgment
    (transcription : NumberedFaceTranscription)
    (audit : FaceDerivedTableAudit transcription) :
    transcription.numberedPackage.TableJudgment transcription.cageMolecule := by
  refine ⟨by simp [NumberedFaceTranscription.numberedPackage,
      NumberedFaceTranscription.atomsByLocant, List.nodup_range],
    audit.edgeTableNodup, ?_, ?_⟩
  · intro edge edgePresent
    rcases edge with ⟨left, right⟩
    change (left, right) ∈ transcription.edgeTable at edgePresent
    rw [numberedFaceTranscription_mem_edgeTable_iff] at edgePresent
    exact ⟨edgePresent.2.2.1, by
      simp [NumberedFaceTranscription.numberedPackage,
        MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.atomsByLocant, edgePresent.1], by
      simp [NumberedFaceTranscription.numberedPackage,
        MolecularFullereneNumberedCagePackage.carrier,
        NumberedFaceTranscription.atomsByLocant, edgePresent.2.1]⟩
  · ext edge
    rcases edge with ⟨left, right⟩
    simp only [List.mem_toFinset]
    change (left, right) ∈ transcription.edgeTable ↔
      (left, right) ∈ molecularFullereneCageEdges transcription.cageMolecule
        transcription.numberedPackage.carrier
    rw [numberedFaceTranscription_mem_edgeTable_iff]
    simp only [molecularFullereneCageEdges, Finset.mem_filter, Finset.mem_product,
      MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.numberedPackage,
      NumberedFaceTranscription.atomsByLocant, List.mem_toFinset, List.mem_range]
    constructor
    · rintro ⟨leftBound, rightBound, ordered, _faceEdge⟩
      refine ⟨⟨leftBound, rightBound⟩, ordered, ?_⟩
      apply (transcription.cageMolecule.bondOrder_pos_iff_exists_bond
        (Nat.ne_of_lt ordered)).mpr
      refine ⟨NumberedFaceTranscription.singleBond (left, right), ?_, ?_⟩
      · change NumberedFaceTranscription.singleBond (left, right) ∈
          transcription.edgeTable.map NumberedFaceTranscription.singleBond
        apply List.mem_map.mpr
        exact ⟨(left, right),
          (numberedFaceTranscription_mem_edgeTable_iff transcription left right).mpr
            ⟨leftBound, rightBound, ordered, _faceEdge⟩, rfl⟩
      · simp [NumberedFaceTranscription.singleBond, RawBond.connects]
    · rintro ⟨⟨leftBound, rightBound⟩, ordered, positive⟩
      have raw := (transcription.cageMolecule.bondOrder_pos_iff_exists_bond
        (Nat.ne_of_lt ordered)).mp positive
      rcases raw with ⟨bond, bondPresent, connects⟩
      simp only [NumberedFaceTranscription.cageMolecule, List.mem_map] at bondPresent
      rcases bondPresent with ⟨sourceEdge, sourcePresent, rfl⟩
      have sourceOrdered := (numberedFaceTranscription_mem_edgeTable_iff
          transcription sourceEdge.1 sourceEdge.2).mp
        sourcePresent |>.2.2.1
      simp only [NumberedFaceTranscription.singleBond, RawBond.connects,
        Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
      rcases connects with forward | reverse
      · have sourceEq : sourceEdge = (left, right) := by
          cases sourceEdge
          simp only [Prod.mk.injEq]
          exact ⟨forward.1, forward.2⟩
        subst sourceEdge
        exact ⟨leftBound, rightBound, ordered,
          ((numberedFaceTranscription_mem_edgeTable_iff transcription left right).mp
            sourcePresent).2.2.2⟩
      · have impossible : right < left := by simpa [reverse.1, reverse.2] using sourceOrdered
        exact (Nat.not_lt_of_ge (Nat.le_of_lt ordered) impossible).elim



private theorem exists_mem_of_countP_pos {Alpha : Type*}
    (predicate : Alpha → Bool) (values : List Alpha)
    (positive : 0 < values.countP predicate) :
    ∃ value ∈ values, predicate value = true := by
  induction values with
  | nil => simp at positive
  | cons head tail inductionHypothesis =>
      by_cases headAccepted : predicate head = true
      · exact ⟨head, by simp, headAccepted⟩
      · have tailPositive : 0 < tail.countP predicate := by
          simpa [List.countP_cons, headAccepted] using positive
        rcases inductionHypothesis tailPositive with ⟨value, present, accepted⟩
        exact ⟨value, by simp [present], accepted⟩

theorem countP_namedFaceEdge_eq_executable
    (faces : List (List Nat)) (facesNodup : ∀ face ∈ faces, face.Nodup)
    (left right : Nat) :
    faces.countP (fun face => decide (IsNamedCycleEdge face left right)) =
      faces.countP (fun face => molecularFullereneNamedFaceEdge? face left right) := by
  induction faces with
  | nil => rfl
  | cons face rest inductionHypothesis =>
      have faceNodup := facesNodup face (by simp)
      have restNodup : ∀ candidate ∈ rest, candidate.Nodup := by
        intro candidate present
        exact facesNodup candidate (by simp [present])
      simp only [List.countP_cons]
      have predicateEq : decide (IsNamedCycleEdge face left right) =
          molecularFullereneNamedFaceEdge? face left right := by
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq]
        exact (molecularFullereneNamedFaceEdge?_eq_true_iff face
          faceNodup left right).symm
      rw [predicateEq, inductionHypothesis restNodup]

theorem countP_forwardFaceEdge_eq_executable
    (faces : List (List Nat)) (left right : Nat) :
    faces.countP (fun face => decide (IsForwardNamedCycleEdge face left right)) =
      faces.countP (fun face => isForwardMolecularFullereneFaceEdge face left right) := by
  apply congrArg (fun predicate => faces.countP predicate)
  funext face
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact (isForwardMolecularFullereneFaceEdge_eq_true_iff face left right).symm





structure FiniteOrientedFaceMapAudit
    (transcription : NumberedFaceTranscription) where
  table : FaceDerivedTableAudit transcription
  connected : MolecularFullereneCageConnected transcription.cageMolecule
    transcription.numberedPackage.carrier
  minimumSize : 20 ≤ transcription.numberedPackage.carrier.card
  carbonAtoms : ∀ atom ∈ transcription.numberedPackage.carrier,
    ∃ spec, transcription.cageMolecule.atomAt? atom = some spec ∧ spec.element = .C
  cubic : ∀ atom ∈ transcription.numberedPackage.carrier,
    (molecularFullereneCageNeighbors transcription.cageMolecule
      transcription.numberedPackage.carrier atom).card = 3
  facesNodup :
    (transcription.numberedPackage.faces.map List.toFinset).Nodup
  facesAccepted : transcription.numberedPackage.faces.all
    (independentP94RingTraversalAccepted transcription.cageMolecule) = true
  faceSizes : ∀ face ∈ transcription.numberedPackage.faces,
    face.length = 5 ∨ face.length = 6
  facesCover : ∀ atom,
    atom ∈ transcription.numberedPackage.carrier ↔
      ∃ face ∈ transcription.numberedPackage.faces, atom ∈ face
  twelvePentagons : transcription.numberedPackage.faces.countP
    (fun face => decide (face.length = 5)) = 12
  hexagonCount : transcription.numberedPackage.faces.countP
    (fun face => decide (face.length = 6)) =
      transcription.numberedPackage.carrier.card / 2 - 10
  twoFacesForListedEdges : transcription.numberedPackage.edgeTable.all (fun edge =>
    decide (transcription.numberedPackage.faces.countP
      (fun face => molecularFullereneNamedFaceEdge? face edge.1 edge.2) = 2)) = true
  oppositeOrientationsForListedEdges : transcription.numberedPackage.edgeTable.all (fun edge =>
    decide (transcription.numberedPackage.faces.countP
          (fun face => isForwardMolecularFullereneFaceEdge face edge.1 edge.2) = 1 ∧
      transcription.numberedPackage.faces.countP
          (fun face => isForwardMolecularFullereneFaceEdge face edge.2 edge.1) = 1)) = true
  eulerCharacteristicTwo :
    transcription.numberedPackage.carrier.card +
        transcription.numberedPackage.faces.length =
      (molecularFullereneCageEdges transcription.cageMolecule
        transcription.numberedPackage.carrier).card + 2




theorem FiniteOrientedFaceMapAudit.toOriented
    (transcription : NumberedFaceTranscription)
    (audit : FiniteOrientedFaceMapAudit transcription) :
    OrientedMolecularFullereneFaceMapJudgment transcription.cageMolecule
      transcription.numberedPackage.topologyInput := by
  have tableJudged := audit.table.tableJudgment transcription
  have facesValid : ∀ face ∈ transcription.numberedPackage.faces,
      MolecularFullereneFaceJudgment transcription.cageMolecule
        transcription.numberedPackage.carrier face := by
    intro face facePresent
    have accepted := (List.all_eq_true.mp audit.facesAccepted) face facePresent
    exact ⟨(independentP94RingTraversalAccepted_eq_true_iff
      transcription.cageMolecule face).mp accepted,
      fun atom atomPresent => (audit.facesCover atom).mpr
        ⟨face, facePresent, by simpa using atomPresent⟩,
      audit.faceSizes face facePresent⟩
  have eachFaceNodup : ∀ face ∈ transcription.numberedPackage.faces, face.Nodup := by
    intro face facePresent
    exact ((facesValid face facePresent).1).2.1
  have carrier : MolecularFullereneCarrierJudgment transcription.cageMolecule
      transcription.numberedPackage.topologyInput := {
    minimumSize := audit.minimumSize
    carbonAtoms := audit.carbonAtoms
    cubic := audit.cubic
    connected := audit.connected
    facesNodup := audit.facesNodup
    facesValid := facesValid
    facesCover := audit.facesCover
    twelvePentagons := audit.twelvePentagons
    hexagonCount := audit.hexagonCount
    twoFacesPerCageEdge := by
      intro left leftPresent right rightPresent ordered
      constructor
      · intro positive
        change left ∈ transcription.numberedPackage.carrier at leftPresent
        change right ∈ transcription.numberedPackage.carrier at rightPresent
        have cageEdge : (left, right) ∈ molecularFullereneCageEdges
            transcription.cageMolecule transcription.numberedPackage.carrier := by
          simp [molecularFullereneCageEdges, leftPresent, rightPresent, ordered, positive]
        have listedFinset : (left, right) ∈
            transcription.numberedPackage.edgeTable.toFinset := by
          rw [tableJudged.2.2.2]
          exact cageEdge
        have listed : (left, right) ∈ transcription.numberedPackage.edgeTable := by
          simpa using listedFinset
        have checked := (List.all_eq_true.mp audit.twoFacesForListedEdges)
          (left, right) listed
        change transcription.numberedPackage.faces.countP
          (fun face => decide (IsNamedCycleEdge face left right)) = 2
        rw [countP_namedFaceEdge_eq_executable transcription.numberedPackage.faces
          eachFaceNodup left right]
        exact of_decide_eq_true checked
      · intro counted
        change transcription.numberedPackage.faces.countP
          (fun face => decide (IsNamedCycleEdge face left right)) = 2 at counted
        have countPositive : 0 < transcription.numberedPackage.faces.countP
            (fun face => decide (IsNamedCycleEdge face left right)) := by
          rw [counted]
          decide
        rcases exists_mem_of_countP_pos
            (fun face => decide (IsNamedCycleEdge face left right))
            transcription.numberedPackage.faces countPositive with
          ⟨face, facePresent, namedAccepted⟩
        have named : IsNamedCycleEdge face left right := of_decide_eq_true namedAccepted
        have independent := (facesValid face facePresent).1
        have bonded := (independent.2.2.2.2.2 left
          (named.choose) right (by
            rcases named with ⟨leftMember, nextOrPrev⟩
            rcases nextOrPrev with next | previous
            · exact next ▸ List.next_mem face left leftMember
            · exact previous ▸ List.prev_mem face left leftMember)
          (Nat.ne_of_lt ordered)).mpr named
        exact (transcription.cageMolecule.bondOrder_pos_iff_exists_bond
          (Nat.ne_of_lt ordered)).mpr bonded
    eulerCharacteristicTwo := audit.eulerCharacteristicTwo }
  refine ⟨carrier, ?_⟩
  intro left leftPresent right rightPresent ordered positive
  change left ∈ transcription.numberedPackage.carrier at leftPresent
  change right ∈ transcription.numberedPackage.carrier at rightPresent
  have cageEdge : (left, right) ∈ molecularFullereneCageEdges
      transcription.cageMolecule transcription.numberedPackage.carrier := by
    simp [molecularFullereneCageEdges, leftPresent, rightPresent, ordered, positive]
  have listedFinset : (left, right) ∈
      transcription.numberedPackage.edgeTable.toFinset := by
    rw [tableJudged.2.2.2]
    exact cageEdge
  have listed : (left, right) ∈ transcription.numberedPackage.edgeTable := by
    simpa using listedFinset
  have checked := of_decide_eq_true
    ((List.all_eq_true.mp audit.oppositeOrientationsForListedEdges) (left, right) listed)
  constructor
  · rw [countP_forwardFaceEdge_eq_executable]
    exact checked.1
  · rw [countP_forwardFaceEdge_eq_executable]
    exact checked.2


def FiniteOrientedFaceMapAudit.toCertificate
    (transcription : NumberedFaceTranscription)
    (audit : FiniteOrientedFaceMapAudit transcription) :
    transcription.numberedPackage.Certificate transcription.cageMolecule :=
  MolecularFullereneNumberedCagePackage.Certificate.ofJudgments
    transcription.cageMolecule transcription.numberedPackage
    (audit.table.tableJudgment transcription) (audit.toOriented transcription)
end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneNamedFaceEdge?_eq_true_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneCyclicallyBonded?_eq_true_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.independentP94RingTraversalAccepted_eq_true_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneCageConnected_of_allRoutesAccepted
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneCageConnected_of_range_hamiltonian
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.FaceDerivedTableAudit.tableJudgment
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.numberedFaceTranscription_bonded_iff_hasFaceEdge
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.numberedFaceTranscription_cageNeighbors_eq_faceNeighbors
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.cycleCarrier_of_cyclicallyBonded
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.independentP94RingTraversal_of_sourceFace
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.independentP94RingTraversal_of_sourceFaceEdges
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.FiniteOrientedFaceMapAudit.toOriented
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.FiniteOrientedFaceMapAudit.toCertificate
