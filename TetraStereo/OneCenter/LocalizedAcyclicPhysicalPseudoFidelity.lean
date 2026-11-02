import TetraStereo.OneCenter.LocalizedOccurrenceRule45Exact
import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.OneCenter.LocalizedConstitutionalFrameNormalization
import TetraStereo.OneCenter.LocalizedNoDoubleWholeStateRule45Bridge
import TetraStereo.OneCenter.LocalizedTerminalTwinAuxiliaryRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry

noncomputable section

/-! ## Lowercase case of an actual tetrahedral label -/

/-- The lowercase (pseudoasymmetric) case of a localized tetrahedral descriptor.  This is the
case constructor, not the `r/s` letter: spatial reflection exchanges `r` and `s` but preserves
the case. -/
def LocalizedTetrahedralRSPseudoDescriptor.IsLowercase :
    LocalizedTetrahedralRSPseudoDescriptor → Prop
  | .chiral _ => False
  | .pseudoasymmetric _ => True

/-- Complementing the label preserves its lowercase/uppercase case. -/
theorem LocalizedTetrahedralRSPseudoDescriptor.isLowercase_swap_iff
    (label : LocalizedTetrahedralRSPseudoDescriptor) :
    label.swap.IsLowercase ↔ label.IsLowercase := by
  cases label with
  | chiral descriptor => cases descriptor <;> rfl
  | pseudoasymmetric descriptor => cases descriptor <;> rfl

/-- The actual classifier is lowercase exactly when exactly one pseudo comparison was recorded. -/
theorem isLowercase_classify_iff (descriptor : RS) (pseudoComparisons : ℕ) :
    (classifyTetrahedralRSPseudo descriptor pseudoComparisons).IsLowercase ↔
      pseudoComparisons = 1 := by
  by_cases one : pseudoComparisons = 1
  · simp [classifyTetrahedralRSPseudo, one,
      LocalizedTetrahedralRSPseudoDescriptor.IsLowercase]
  · simp [classifyTetrahedralRSPseudo, one,
      LocalizedTetrahedralRSPseudoDescriptor.IsLowercase]





























































/-! ## Actual graph structure: rigidity versus a physical terminal Twin pair -/

/-- A distinguished center is constitutionally rigid when every multi-center automorphism that
fixes it also fixes all four ligand positions.  This is a graph-level predicate on the actual
certified molecule. -/
def ConstitutionallyRigid {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (d : m.Center) : Prop :=
  ∀ e : m.Aut, m.centerPerm e d = d → m.ligandPermAt e d = 1





def TerminalTwinPair {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (d : m.Center) : Prop :=
  ∃ e : m.Aut, m.centerPerm e d = d ∧
    ∃ a b : Fin 4, a ≠ b ∧
      m.ligandPermAt e d a = b ∧
      m.ligandPermAt e d b = a ∧
      (∀ k : Fin 4, k ≠ a → k ≠ b → m.ligandPermAt e d k = k) ∧
      m.mol.atomZ (m.ligandAtomAt d a) = m.mol.atomZ (m.ligandAtomAt d b) ∧
      Fintype.card (m.mol.Neighbor (m.ligandAtomAt d a)) = 1 ∧
      Fintype.card (m.mol.Neighbor (m.ligandAtomAt d b)) = 1

/-- A terminal twin pair is incompatible with constitutional rigidity: the twin automorphism
exhibits a nontrivial ligand permutation.  Hence the nonroot inventory "rigid or terminal twin"
is a disjoint union. -/
theorem terminalTwinPair_not_constitutionallyRigid
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {d : m.Center}
    (twin : TerminalTwinPair m d) :
    ¬ ConstitutionallyRigid m d := by
  rintro rigid
  obtain ⟨e, centerFixed, a, b, distinct, mapsA, -, -, -, -, -⟩ := twin
  have permutationsEqual : m.ligandPermAt e d = 1 := rigid e centerFixed
  have imagesEqual : b = a := by
    have image : m.ligandPermAt e d a = (1 : Equiv.Perm (Fin 4)) a :=
      congrArg (fun permutation : Equiv.Perm (Fin 4) => permutation a) permutationsEqual
    simpa [mapsA] using image
  exact distinct imagesEqual.symm

/-! ## Acyclicity forces pairwise disjoint root branches -/

/-- The deleted-root ligand branches of an actual acyclic certified molecule are pairwise
disjoint.  The proof takes two branch walks avoiding the center, converts them to simple paths,
concatenates them into a path between the two ligand atoms that still avoids the center, and
compares it with the direct simple path through the center using acyclicity (`path_unique`).

Consequently `PairwiseDisjointLigandBranches` is not an independent chemical assumption on the
acyclic single-bond domain. -/
theorem pairwiseDisjointLigandBranches_of_acyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (c : m.Center) (acyclic : m.mol.Acyclic) :
    PairwiseDisjointLigandBranches m c := by
  intro i j distinct v ⟨p, pAvoids⟩ ⟨q, qAvoids⟩
  let G := m.mol.underlyingSimpleGraph
  have pPathAvoids : c.1 ∉ (p.toPath : G.Walk (m.ligandAtomAt c i) v).support :=
    fun member => pAvoids ((SimpleGraph.Walk.support_toPath_subset p) member)
  have qPathAvoids : c.1 ∉ (q.toPath : G.Walk (m.ligandAtomAt c j) v).support :=
    fun member => qAvoids ((SimpleGraph.Walk.support_toPath_subset q) member)
  let branchWalk : G.Walk (m.ligandAtomAt c i) (m.ligandAtomAt c j) :=
    (p.toPath : G.Walk (m.ligandAtomAt c i) v).append
      (q.toPath : G.Walk (m.ligandAtomAt c j) v).reverse
  have branchWalkAvoids : c.1 ∉ branchWalk.support := by
    intro member
    rw [SimpleGraph.Walk.mem_support_append_iff] at member
    rcases member with inP | inQ
    · exact pPathAvoids inP
    · rw [SimpleGraph.Walk.support_reverse] at inQ
      exact qPathAvoids (List.mem_reverse.mp inQ)
  let branchPath : G.Path (m.ligandAtomAt c i) (m.ligandAtomAt c j) := branchWalk.toPath
  have branchPathAvoids :
      c.1 ∉ (branchPath : G.Walk (m.ligandAtomAt c i) (m.ligandAtomAt c j)).support :=
    fun member => branchWalkAvoids ((SimpleGraph.Walk.support_toPath_subset branchWalk) member)
  have atomDistinct : m.ligandAtomAt c i ≠ m.ligandAtomAt c j :=
    fun equal => distinct (m.ligandAtomAt_injective c equal)
  let ai := m.ligandAtomAt c i
  let aj := m.ligandAtomAt c j
  have aiCenter : G.Adj ai c.1 := G.symm (m.ligandAtomAt_adj c i)
  have centerAj : G.Adj c.1 aj := m.ligandAtomAt_adj c j
  have tailPath :
      (SimpleGraph.Walk.cons centerAj (SimpleGraph.Walk.nil : G.Walk aj aj)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    intro member
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at member
    exact (ligandAtomAt_ne_center m c j) member.symm
  have directPath : (SimpleGraph.Walk.cons aiCenter
      (SimpleGraph.Walk.cons centerAj (SimpleGraph.Walk.nil : G.Walk aj aj))).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨tailPath, ?_⟩
    intro member
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.mem_singleton] at member
    rcases member with atCenter | atAtom
    · exact (ligandAtomAt_ne_center m c i) atCenter
    · exact atomDistinct (by simpa [ai, aj] using atAtom)
  let direct : G.Path ai aj := ⟨_, directPath⟩
  have centerInDirect : c.1 ∈ (direct : G.Walk ai aj).support := by
    change c.1 ∈ (SimpleGraph.Walk.cons aiCenter
      (SimpleGraph.Walk.cons centerAj (SimpleGraph.Walk.nil : G.Walk aj aj))).support
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil]
    simp
  have pathsEqual : (branchPath : G.Walk ai aj) = (direct : G.Walk ai aj) :=
    congrArg Subtype.val (m.mol.acyclic_path_unique acyclic branchPath direct)
  have centerInBranch : c.1 ∈ (branchPath : G.Walk ai aj).support := by
    rw [pathsEqual]
    exact centerInDirect
  exact branchPathAvoids centerInBranch

/-- Tree-likeness (acyclicity together with single bonds) supplies pairwise disjoint root
branches.  This is the form that removes the named hypothesis from the rooted branch framework. -/
theorem pairwiseDisjointLigandBranches_of_treeLike
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (c : m.Center) (treeLike : m.mol.TreeLike) :
    PairwiseDisjointLigandBranches m c :=
  pairwiseDisjointLigandBranches_of_acyclic m c treeLike.1

/-! ## Exact decomposition of the actual occurrence evaluator -/

/-- A successful safe occurrence tracked order is exactly a successful actual tracked sort plus a
successful all-pairs coherence check, with the same stored order and count. -/
theorem safeLocalizedOccurrenceRule45TrackedOrder?_decompose
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : input.safeLocalizedOccurrenceRule45TrackedOrder?
      target view frame = some tracked) :
    input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ∧
      input.localizedOccurrenceRule45OrderCoherent?
        target view frame tracked.highestFirst = true := by
  unfold safeLocalizedOccurrenceRule45TrackedOrder? at computed
  cases sorted : input.localizedOccurrenceRule45TrackedOrder? target view frame with
  | none => simp [sorted] at computed
  | some observed =>
      cases coherent : input.localizedOccurrenceRule45OrderCoherent?
          target view frame observed.highestFirst with
      | false => simp [sorted, coherent] at computed
      | true =>
          simp [sorted, coherent] at computed
          subst tracked
          exact ⟨rfl, coherent⟩

/-- Successful occurrence spatial evidence stores exactly the safe tracked order obtained from
its frame.  This exposes the actual comparator used by the evidence. -/
theorem localizedOccurrenceRule45SpatialEvidence?_safe_tracked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel)
    (computed : input.localizedOccurrenceRule45SpatialEvidence? target view = some evidence) :
    input.safeLocalizedOccurrenceRule45TrackedOrder?
        target view evidence.frame = some evidence.tracked := by
  exact
    (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
      target view evidence.frame evidence.tracked).mpr
      ((input.localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
        target view evidence).mp computed).2.2.1

/-- Exact decomposition of the actual occurrence descriptor: the evidence, the actual tracked
sort over `compareLocalizedOccurrenceThroughRule5At?`, the coherence check, the actual points, and
the actual classification.  Nothing is replaced by a synthetic comparator. -/
theorem localizedOccurrenceRule45Descriptor?_decompose
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceRule45Descriptor? target view = some descriptor) :
    ∃ evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel,
      ∃ raw : RS,
        input.localizedOccurrenceRule45SpatialEvidence? target view = some evidence ∧
          input.localizedOccurrenceRule45TrackedOrder?
              target view evidence.frame = some evidence.tracked ∧
          input.localizedOccurrenceRule45OrderCoherent? target view evidence.frame
              evidence.tracked.highestFirst = true ∧
          descriptorOfPriorityOrderedPoints? evidence.points = some raw ∧
          descriptor =
            classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons := by
  obtain ⟨evidence, raw, canonicalEvidence, rationalRaw, classifyEqual⟩ :=
    (input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
      target view descriptor).mp computed
  have evidenceComputed : input.localizedOccurrenceRule45SpatialEvidence?
      target view = some evidence :=
    (input.localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
      target view evidence).mpr canonicalEvidence
  have safeComputed : input.safeLocalizedOccurrenceRule45TrackedOrder?
      target view evidence.frame = some evidence.tracked :=
    (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
      target view evidence.frame evidence.tracked).mpr canonicalEvidence.2.2.1
  have safeDecomposition :=
    safeLocalizedOccurrenceRule45TrackedOrder?_decompose
      input target view evidence.frame evidence.tracked safeComputed
  have rawComputed : descriptorOfPriorityOrderedPoints? evidence.points = some raw :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff evidence.points raw).mpr rationalRaw
  exact ⟨evidence, raw, evidenceComputed, safeDecomposition.1, safeDecomposition.2,
    rawComputed, classifyEqual⟩

/-- The actual occurrence descriptor is lowercase exactly when the actual tracked sort recorded
exactly one pseudo comparison.  This is an unconditional fact about the actual evaluator; it does
not assert that the recorded count has the chemical reading required by P-92. -/
theorem localizedOccurrenceRule45Descriptor?_isLowercase_iff_evidence_count
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceRule45Descriptor? target view = some descriptor) :
    LocalizedTetrahedralRSPseudoDescriptor.IsLowercase descriptor ↔
      ∃ evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel,
        input.localizedOccurrenceRule45SpatialEvidence? target view = some evidence ∧
          evidence.tracked.pseudoComparisons = 1 := by
  obtain ⟨evidence, raw, evidenceComputed, -, -, rawComputed, classifyEqual⟩ :=
    localizedOccurrenceRule45Descriptor?_decompose input target view descriptor computed
  constructor
  · intro lowercase
    have countOne : evidence.tracked.pseudoComparisons = 1 := by
      apply (isLowercase_classify_iff raw evidence.tracked.pseudoComparisons).1
      rw [← classifyEqual]
      exact lowercase
    exact ⟨evidence, evidenceComputed, countOne⟩
  · rintro ⟨otherEvidence, otherComputed, otherCount⟩
    have sameEvidence : otherEvidence = evidence :=
      Option.some.inj (otherComputed.symm.trans evidenceComputed)
    have evidenceCount : evidence.tracked.pseudoComparisons = 1 := by
      rw [← sameEvidence]
      exact otherCount
    rw [classifyEqual]
    exact (isLowercase_classify_iff raw evidence.tracked.pseudoComparisons).2 evidenceCount

/-! ## The actual occurrence pseudo signal

The production occurrence comparator is the compound Rule-4a--5 comparator applied to the two
actual reroot keys.  The following decomposition exposes that reduction without replacing any
definition, and then rewrites the compound `pseudo` flag with its exact actual signal law. -/

/-- The actual occurrence `pseudo` flag is the compound through-Rule-5 `pseudo` flag of the two
actual reroot keys built at the two frame cursors. -/
theorem compareLocalizedOccurrenceThroughRule5At?_pseudo_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison)
    (computed : input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right = some result) :
    result.pseudo = true ↔
      ∃ leftKey rightKey : input.LocalizedRerootCompoundRule45Key,
        input.buildLocalizedRerootCompoundRule45Key? target view
            (localizedOccurrenceRerootEvaluationFuel carrierFuel)
            (frame.cursorAt left) = some leftKey ∧
        input.buildLocalizedRerootCompoundRule45Key? target view
            (localizedOccurrenceRerootEvaluationFuel carrierFuel)
            (frame.cursorAt right) = some rightKey ∧
        (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).pseudo = true := by
  unfold compareLocalizedOccurrenceThroughRule5At? at computed
  cases leftComputed : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) with
  | none => simp [leftComputed] at computed
  | some leftKey =>
      cases rightComputed : input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) with
      | none => simp [leftComputed, rightComputed] at computed
      | some rightKey =>
          have resultEq : localizedOccurrenceRule45ComparisonRecord
              (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey) = result := by
            simpa [leftComputed, rightComputed] using computed
          subst result
          constructor
          · intro pseudo
            exact ⟨leftKey, rightKey, rfl, rfl, by
              simpa [localizedOccurrenceRule45ComparisonRecord] using pseudo⟩
          · rintro ⟨otherLeft, otherRight, otherLeftComputed, otherRightComputed, pseudo⟩
            have leftEq : otherLeft = leftKey :=
              (Option.some.inj otherLeftComputed).symm
            have rightEq : otherRight = rightKey :=
              (Option.some.inj otherRightComputed).symm
            subst otherLeft
            subst otherRight
            simpa [localizedOccurrenceRule45ComparisonRecord] using pseudo

/-- Exact actual signal law at the occurrence level: the production `pseudo` flag is true exactly
when the two actual reroot keys tie throughout Rules 4b/4c, the common-`R` Rule-5 reading
comparison is strict, and the common-`S` reading disagrees with the common-`R` reading. -/
theorem compareLocalizedOccurrenceThroughRule5At?_pseudo_iff_prior_tie_readings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison)
    (computed : input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right = some result) :
    result.pseudo = true ↔
      ∃ leftKey rightKey : input.LocalizedRerootCompoundRule45Key,
        input.buildLocalizedRerootCompoundRule45Key? target view
            (localizedOccurrenceRerootEvaluationFuel carrierFuel)
            (frame.cursorAt left) = some leftKey ∧
        input.buildLocalizedRerootCompoundRule45Key? target view
            (localizedOccurrenceRerootEvaluationFuel carrierFuel)
            (frame.cursorAt right) = some rightKey ∧
        input.compareLocalizedRerootCompoundRule4bcKeys leftKey.prior rightKey.prior =
            Ordering.eq ∧
        input.compareLocalizedRerootCompoundRule5Readings .R
            leftKey.rule5Readings rightKey.rule5Readings ≠ Ordering.eq ∧
        input.compareLocalizedRerootCompoundRule5Readings .S
            leftKey.rule5Readings rightKey.rule5Readings ≠
          input.compareLocalizedRerootCompoundRule5Readings .R
            leftKey.rule5Readings rightKey.rule5Readings := by
  rw [compareLocalizedOccurrenceThroughRule5At?_pseudo_iff input target view frame left right
    result computed]
  constructor
  · rintro ⟨leftKey, rightKey, leftComputed, rightComputed, pseudo⟩
    exact ⟨leftKey, rightKey, leftComputed, rightComputed,
      (LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
        input leftKey rightKey).mp pseudo⟩
  · rintro ⟨leftKey, rightKey, leftComputed, rightComputed, signal⟩
    exact ⟨leftKey, rightKey, leftComputed, rightComputed,
      (LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
        input leftKey rightKey).mpr signal⟩

/-! ## Exact spatial reflection -/

/-- Reflection of a rational point through the plane `x = 0`. -/
def CartesianPoint3.reflectX (point : CartesianPoint3) : CartesianPoint3 :=
  ⟨-point.x, point.y, point.z⟩

/-- Reflection is an involution. -/
theorem CartesianPoint3.reflectX_involutive (point : CartesianPoint3) :
    CartesianPoint3.reflectX (CartesianPoint3.reflectX point) = point := by
  rcases point with ⟨x, y, z⟩
  simp [CartesianPoint3.reflectX]

/-- Exact oriented volume changes sign under reflection through `x = 0`. -/
theorem CartesianPoint3.orientedVolume_reflectX
    (first second third fourth : CartesianPoint3) :
    CartesianPoint3.orientedVolume
        (CartesianPoint3.reflectX first) (CartesianPoint3.reflectX second)
        (CartesianPoint3.reflectX third) (CartesianPoint3.reflectX fourth) =
      -CartesianPoint3.orientedVolume first second third fourth := by
  simp only [CartesianPoint3.orientedVolume, CartesianPoint3.reflectX]
  ring

/-- The exact geometric `R/S` reader is equivariant under reflection, complemented by `RS.swap`. -/
theorem descriptorOfOrientedVolume?_neg (volume : ℚ) :
    descriptorOfOrientedVolume? (-volume) =
      (descriptorOfOrientedVolume? volume).map RS.swap := by
  unfold descriptorOfOrientedVolume?
  by_cases negative : volume < 0
  · have positive' : 0 < -volume := neg_pos.mpr negative
    have notNegative' : ¬ -volume < 0 := not_lt.mpr (le_of_lt positive')
    rw [if_neg notNegative', if_pos positive', if_pos negative]
    simp [RS.swap]
  · by_cases positive : 0 < volume
    · have negative' : -volume < 0 := neg_lt_zero.mpr positive
      have notPositive' : ¬ 0 < -volume := not_lt.mpr (le_of_lt negative')
      rw [if_pos negative', if_neg (not_lt.mpr (le_of_lt positive)), if_pos positive]
      simp [RS.swap]
    · have zero : volume = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      subst volume
      simp

/-- Reflecting priority-ordered points swaps the exact `R/S` descriptor produced by the actual
reader `descriptorOfPriorityOrderedPoints?`. -/
theorem descriptorOfPriorityOrderedPoints?_reflectX (points : List CartesianPoint3) :
    descriptorOfPriorityOrderedPoints?
        (points.map CartesianPoint3.reflectX) =
      (descriptorOfPriorityOrderedPoints? points).map RS.swap := by
  cases points with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth rest =>
                  cases rest with
                  | nil =>
                      simp [descriptorOfPriorityOrderedPoints?,
                        CartesianPoint3.orientedVolume_reflectX,
                        descriptorOfOrientedVolume?_neg]
                  | cons fifth rest => rfl

/-- The actual classification commutes with reflection: the reflected point list yields the
swapped descriptor, while the pseudo-comparison count is unchanged. -/
theorem classifier_reflectX (points : List CartesianPoint3) (pseudoComparisons : ℕ) :
    (descriptorOfPriorityOrderedPoints? (points.map CartesianPoint3.reflectX)).map
        (fun raw => classifyTetrahedralRSPseudo raw pseudoComparisons) =
      (descriptorOfPriorityOrderedPoints? points).map
        (fun raw => (classifyTetrahedralRSPseudo raw pseudoComparisons).swap) := by
  rw [descriptorOfPriorityOrderedPoints?_reflectX]
  cases computed : descriptorOfPriorityOrderedPoints? points with
  | none => rfl
  | some raw =>
      simp [classifyTetrahedralRSPseudo_swap]






theorem classifier_reflectX_preserves_lowercase
    (points : List CartesianPoint3) (pseudoComparisons : ℕ) :
    (match descriptorOfPriorityOrderedPoints? (points.map CartesianPoint3.reflectX) with
      | some raw => LocalizedTetrahedralRSPseudoDescriptor.IsLowercase
          (classifyTetrahedralRSPseudo raw pseudoComparisons)
      | none => False) ↔
    (match descriptorOfPriorityOrderedPoints? points with
      | some raw => LocalizedTetrahedralRSPseudoDescriptor.IsLowercase
          (classifyTetrahedralRSPseudo raw pseudoComparisons)
      | none => False) := by
  rw [descriptorOfPriorityOrderedPoints?_reflectX]
  cases computed : descriptorOfPriorityOrderedPoints? points with
  | none => rfl
  | some raw =>
      simp [classifyTetrahedralRSPseudo_swap,
        LocalizedTetrahedralRSPseudoDescriptor.isLowercase_swap_iff]














theorem referenceState_reader_eq_chiral_of_physicalFrame
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (parity : TetrahedralInputParity)
    (writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity) :
    ∃ tracked : TrackedLocalizedLigandOrder,
      input.certified.localizedOccurrenceRule45TrackedOrder? target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
      tracked.pseudoComparisons = 0 ∧
      LocalizedUniversalReference.referenceState input target =
        some (.chiral (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven (tracked.highestFirst.map Fin.val)))) := by
  exact
    input.certified.localizedCIPModel_reader_eq_chiral_of_physicalFrame
      (input.certified.localizedOccurrenceRule45AuxiliarySemantics
        (LocalizedUniversalReference.carrierFuel input))
      (LocalizedUniversalReference.referenceState input)
      (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
        input noDouble)
      target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target)
      frame derived separated center centerReal pointsAt spatial parity writtenParity
      rfl












theorem referenceState_reader_eq_none_of_actualPhysical_terminalTwins
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame)
    (leftIndex rightIndex : Fin 4)
    (leftCursor rightCursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (leftAt : frame.cursorAt leftIndex = leftCursor)
    (rightAt : frame.cursorAt rightIndex = rightCursor)
    (leftOutward : leftCursor.occurrence.1 ∈
      input.certified.localizedCarrierOutwardChildFrames
        (fuel := LocalizedUniversalReference.carrierFuel input) target.1)
    (rightOutward : rightCursor.occurrence.1 ∈
      input.certified.localizedCarrierOutwardChildFrames
        (fuel := LocalizedUniversalReference.carrierFuel input) target.1)
    (cursorDistinct : leftCursor ≠ rightCursor)
    (centerAtom leftAtom rightAtom : input.certified.Atom)
    (leftActual : input.certified.ActualPhysicalAtomAtNode leftCursor.occurrence.1.node leftAtom)
    (rightActual : input.certified.ActualPhysicalAtomAtNode rightCursor.occurrence.1.node rightAtom)
    (leftParentObserved : leftCursor.occurrence.1.node.parent? = some centerAtom)
    (rightParentObserved : rightCursor.occurrence.1.node.parent? = some centerAtom)
    (leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {centerAtom})
    (rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {centerAtom})
    (leftSingleBond : input.certified.moleculeGraph.bond leftAtom centerAtom = 1)
    (rightSingleBond : input.certified.moleculeGraph.bond rightAtom centerAtom = 1)
    (leftNonduplicate : leftCursor.occurrence.1.node.isDuplicateLeaf = false)
    (rightNonduplicate : rightCursor.occurrence.1.node.isDuplicateLeaf = false)
    (zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom)
    (massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom)
    (distanceEq : leftCursor.occurrence.1.node.rule1bRootDistance =
      rightCursor.occurrence.1.node.rule1bRootDistance) :
    LocalizedUniversalReference.referenceState input target = none := by
  have descriptorNone :=
    CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal.localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_terminalTwins
      input.certified
      (fuel := LocalizedUniversalReference.carrierFuel input)
      target (LocalizedUniversalReference.referenceState input)
      (LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
        input noDouble)
      frame frameComputed leftIndex rightIndex leftCursor rightCursor leftAt rightAt
      leftOutward rightOutward cursorDistinct centerAtom leftAtom rightAtom
      leftActual rightActual leftParentObserved rightParentObserved
      leftNeighbors rightNeighbors leftSingleBond rightSingleBond
      leftNonduplicate rightNonduplicate zEq massEq distanceEq
  rw [LocalizedUniversalReference.referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
    input noDouble target]
  exact descriptorNone

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedTetrahedralRSPseudoDescriptor.IsLowercase
assert_kernel_only TetraStereo.OneCenter.LocalizedTetrahedralRSPseudoDescriptor.isLowercase_swap_iff
assert_kernel_only TetraStereo.OneCenter.isLowercase_classify_iff
assert_kernel_only TetraStereo.OneCenter.ConstitutionallyRigid
assert_kernel_only TetraStereo.OneCenter.TerminalTwinPair
assert_kernel_only TetraStereo.OneCenter.terminalTwinPair_not_constitutionallyRigid
assert_kernel_only TetraStereo.OneCenter.pairwiseDisjointLigandBranches_of_acyclic
assert_kernel_only TetraStereo.OneCenter.pairwiseDisjointLigandBranches_of_treeLike
assert_kernel_only TetraStereo.OneCenter.safeLocalizedOccurrenceRule45TrackedOrder?_decompose
assert_kernel_only TetraStereo.OneCenter.localizedOccurrenceRule45SpatialEvidence?_safe_tracked
assert_kernel_only TetraStereo.OneCenter.localizedOccurrenceRule45Descriptor?_decompose
assert_kernel_only TetraStereo.OneCenter.localizedOccurrenceRule45Descriptor?_isLowercase_iff_evidence_count
assert_kernel_only TetraStereo.OneCenter.compareLocalizedOccurrenceThroughRule5At?_pseudo_iff
assert_kernel_only TetraStereo.OneCenter.compareLocalizedOccurrenceThroughRule5At?_pseudo_iff_prior_tie_readings
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.reflectX
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.reflectX_involutive
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.orientedVolume_reflectX
assert_kernel_only TetraStereo.OneCenter.descriptorOfOrientedVolume?_neg
assert_kernel_only TetraStereo.OneCenter.descriptorOfPriorityOrderedPoints?_reflectX
assert_kernel_only TetraStereo.OneCenter.classifier_reflectX
assert_kernel_only TetraStereo.OneCenter.classifier_reflectX_preserves_lowercase
assert_kernel_only TetraStereo.OneCenter.referenceState_reader_eq_chiral_of_physicalFrame
assert_kernel_only TetraStereo.OneCenter.referenceState_reader_eq_none_of_actualPhysical_terminalTwins

end

end TetraStereo.OneCenter
