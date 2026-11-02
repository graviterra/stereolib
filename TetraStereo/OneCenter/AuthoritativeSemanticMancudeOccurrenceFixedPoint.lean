import TetraStereo.OneCenter.AuthoritativeSemanticMancudePublicTetrahedralAnalysis
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceScheduler
import TetraStereo.OneCenter.LocalizedOccurrenceFixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Source-canonical mancude occurrence fixed point

The canonical mancude child relation was previously used only while compiling constitutional
ligand keys.  This module makes that same source-level relation the topology of a complete finite
occurrence carrier.  In particular, neither written aromatic bond orders nor a selected Kekule
matching occur in the carrier, its dependency relation, or its causal scheduler.

The chemical evaluator remains an explicit integration object: it must provide an independent
complete-outcome derivation relation, a dependency-restricted executable rule, and a proof that
the two agree.  Once supplied, existence, uniqueness, and causal schedulability follow from the
source-canonical depth grading proved here.
-/

namespace AuthoritativeChemicalInput

open DeclarativeCIP

/-- One coordinate in the bounded source-canonical mancude digraph. -/
structure AromaticCanonicalOccurrenceFrame (source : AuthoritativeChemicalInput) where
  root : source.AromaticCanonicalAtom
  address : List Nat
  node : OfficialCIPNode source.AromaticCanonicalAtom
  remaining : Nat
  deriving DecidableEq, Repr

/-- Exact depth-first enumeration under the source-canonical child relation. -/
def aromaticCanonicalOccurrenceSubtree (source : AuthoritativeChemicalInput)
    (root : source.AromaticCanonicalAtom) :
    Nat → List Nat → OfficialCIPNode source.AromaticCanonicalAtom →
      List source.AromaticCanonicalOccurrenceFrame
  | 0, path, node =>
      [{ root := root, address := path, node := node, remaining := 0 }]
  | fuel + 1, path, node =>
      { root := root, address := path, node := node, remaining := fuel + 1 } ::
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount node).zipIdx.flatMap fun child =>
            source.aromaticCanonicalOccurrenceSubtree root fuel
              (path ++ [child.2]) child.1

/-- Independent reachability semantics for the bounded source-canonical subtree. -/
inductive DeclarativeAromaticCanonicalOccurrenceSubtree
    (source : AuthoritativeChemicalInput)
    (root : source.AromaticCanonicalAtom) :
    List Nat → Nat → OfficialCIPNode source.AromaticCanonicalAtom →
      source.AromaticCanonicalOccurrenceFrame → Prop
  | subtreeRoot (path fuel node) :
      DeclarativeAromaticCanonicalOccurrenceSubtree source root path fuel node
        { root := root, address := path, node := node, remaining := fuel }
  | subtreeDescendant {path fuel node child slot occurrence}
      (childAtSlot : (child, slot) ∈
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount node).zipIdx)
      (descendant : DeclarativeAromaticCanonicalOccurrenceSubtree source root
        (path ++ [slot]) fuel child occurrence) :
      DeclarativeAromaticCanonicalOccurrenceSubtree source root
        path (fuel + 1) node occurrence

/-- Enumeration and the independent reachability relation are extensionally exact. -/
theorem mem_aromaticCanonicalOccurrenceSubtree_iff
    (source : AuthoritativeChemicalInput)
    (root : source.AromaticCanonicalAtom) :
    ∀ fuel path node occurrence,
      occurrence ∈ source.aromaticCanonicalOccurrenceSubtree root fuel path node ↔
        source.DeclarativeAromaticCanonicalOccurrenceSubtree
          root path fuel node occurrence
  | 0, path, node, occurrence => by
      constructor
      · intro present
        simp [aromaticCanonicalOccurrenceSubtree] at present
        subst occurrence
        exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot path 0 node
      · intro derived
        cases derived with
        | subtreeRoot => simp [aromaticCanonicalOccurrenceSubtree]
  | fuel + 1, path, node, occurrence => by
      constructor
      · intro present
        rw [aromaticCanonicalOccurrenceSubtree, List.mem_cons] at present
        rcases present with here | below
        · subst occurrence
          exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
            path (fuel + 1) node
        · rw [List.mem_flatMap] at below
          rcases below with ⟨child, childPresent, descendantPresent⟩
          exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeDescendant childPresent
            ((source.mem_aromaticCanonicalOccurrenceSubtree_iff root fuel
              (path ++ [child.2]) child.1 occurrence).mp descendantPresent)
      · intro derived
        cases derived with
        | subtreeRoot => simp [aromaticCanonicalOccurrenceSubtree]
        | @subtreeDescendant _ _ _ child slot occurrence childPresent descendant =>
            rw [aromaticCanonicalOccurrenceSubtree, List.mem_cons]
            apply Or.inr
            rw [List.mem_flatMap]
            exact ⟨(child, slot), childPresent,
              (source.mem_aromaticCanonicalOccurrenceSubtree_iff root fuel
                (path ++ [slot]) child occurrence).mpr descendant⟩

/-- Reachability fixes the stored root. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_root_eq
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    occurrence.root = root := by
  induction derived with
  | subtreeRoot => rfl
  | subtreeDescendant _ _ inductionHypothesis => exact inductionHypothesis

/-- Reachability lies on one exact address/remaining-depth hyperplane. -/
theorem declarativeAromaticCanonicalOccurrenceSubtree_depthGrade
    (source : AuthoritativeChemicalInput)
    {root : source.AromaticCanonicalAtom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    occurrence.address.length + occurrence.remaining = path.length + fuel := by
  induction derived with
  | subtreeRoot => rfl
  | subtreeDescendant _ _ inductionHypothesis =>
      simp only [List.length_append, List.length_singleton] at inductionHypothesis ⊢
      omega

/-- Complete bounded source-canonical subtree rooted at one atom. -/
def aromaticCanonicalOccurrencesAtAtom
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (atom : source.AromaticCanonicalAtom) :
    List source.AromaticCanonicalOccurrenceFrame :=
  source.aromaticCanonicalOccurrenceSubtree atom (fuel + 1) []
    (OfficialCIPNode.root atom)

/-- Independent meaning of membership below one source atom. -/
def DeclarativeAromaticCanonicalOccurrenceAtAtom
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (atom : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOccurrenceFrame → Prop :=
  source.DeclarativeAromaticCanonicalOccurrenceSubtree atom [] (fuel + 1)
    (OfficialCIPNode.root atom)

theorem mem_aromaticCanonicalOccurrencesAtAtom_iff
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (atom : source.AromaticCanonicalAtom)
    (occurrence : source.AromaticCanonicalOccurrenceFrame) :
    occurrence ∈ source.aromaticCanonicalOccurrencesAtAtom fuel atom ↔
      source.DeclarativeAromaticCanonicalOccurrenceAtAtom fuel atom occurrence :=
  source.mem_aromaticCanonicalOccurrenceSubtree_iff atom (fuel + 1) []
    (OfficialCIPNode.root atom) occurrence

/-- Molecule-wide source-canonical occurrence enumeration. -/
def aromaticCanonicalOccurrences
    (source : AuthoritativeChemicalInput) (fuel : Nat) :
    List source.AromaticCanonicalOccurrenceFrame :=
  ((List.finRange source.molecule.atomCount).flatMap
    (source.aromaticCanonicalOccurrencesAtAtom fuel)).dedup

theorem aromaticCanonicalOccurrences_nodup
    (source : AuthoritativeChemicalInput) (fuel : Nat) :
    (source.aromaticCanonicalOccurrences fuel).Nodup :=
  List.nodup_dedup _

/-- Independent molecule-wide source-canonical reachability. -/
def DeclarativeAromaticCanonicalOccurrence
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (occurrence : source.AromaticCanonicalOccurrenceFrame) : Prop :=
  source.DeclarativeAromaticCanonicalOccurrenceAtAtom
    fuel occurrence.root occurrence

/-- The finite molecule-wide enumeration is exactly the independent reachability relation. -/
theorem mem_aromaticCanonicalOccurrences_iff
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (occurrence : source.AromaticCanonicalOccurrenceFrame) :
    occurrence ∈ source.aromaticCanonicalOccurrences fuel ↔
      source.DeclarativeAromaticCanonicalOccurrence fuel occurrence := by
  rw [aromaticCanonicalOccurrences, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨atom, _atomPresent, occurrencePresent⟩
    have derived := (source.mem_aromaticCanonicalOccurrencesAtAtom_iff
      fuel atom occurrence).mp occurrencePresent
    have rootIdentity :=
      source.declarativeAromaticCanonicalOccurrenceSubtree_root_eq derived
    simpa [DeclarativeAromaticCanonicalOccurrence,
      DeclarativeAromaticCanonicalOccurrenceAtAtom, rootIdentity] using derived
  · intro derived
    exact ⟨occurrence.root, by simp,
      (source.mem_aromaticCanonicalOccurrencesAtAtom_iff
        fuel occurrence.root occurrence).mpr derived⟩

/-- Finite proof-relevant source-canonical occurrence carrier. -/
abbrev AromaticCanonicalOccurrence
    (source : AuthoritativeChemicalInput) (fuel : Nat) :=
  { occurrence : source.AromaticCanonicalOccurrenceFrame //
    occurrence ∈ source.aromaticCanonicalOccurrences fuel }

/-- Every carrier member has the exact global depth grading. -/
theorem aromaticCanonicalOccurrence_depthGrade
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    occurrence.1.address.length + occurrence.1.remaining = fuel + 1 := by
  have derived := (source.mem_aromaticCanonicalOccurrences_iff
    fuel occurrence.1).mp occurrence.2
  simpa using source.declarativeAromaticCanonicalOccurrenceSubtree_depthGrade derived

/-- The root occurrence corresponding to a perceived source-canonical tetrahedral center. -/
noncomputable def aromaticCanonicalFinalOccurrence
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalOccurrence fuel := by
  classical
  refine ⟨
    { root := center.1
      address := []
      node := OfficialCIPNode.root center.1
      remaining := fuel + 1 }, ?_⟩
  apply (source.mem_aromaticCanonicalOccurrences_iff fuel _).mpr
  exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
    [] (fuel + 1) (OfficialCIPNode.root center.1)

/-- A descriptor may read only strictly deeper occurrences below the same source root. -/
def AromaticCanonicalDepthDependency
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (dependency target : source.AromaticCanonicalOccurrence fuel) : Prop :=
  dependency.1.root = target.1.root ∧
    target.1.address.length < dependency.1.address.length

instance aromaticCanonicalDepthDependencyDecidable
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (dependency target : source.AromaticCanonicalOccurrence fuel) :
    Decidable (source.AromaticCanonicalDepthDependency dependency target) := by
  unfold AromaticCanonicalDepthDependency
  infer_instance

/-- Strictly deeper source occurrences have strictly less remaining expansion depth. -/
theorem aromaticCanonicalDepthDependency_remaining_lt
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    {dependency target : source.AromaticCanonicalOccurrence fuel}
    (below : source.AromaticCanonicalDepthDependency dependency target) :
    dependency.1.remaining < target.1.remaining := by
  rcases below with ⟨_sameRoot, deeper⟩
  have dependencyGrade := source.aromaticCanonicalOccurrence_depthGrade dependency
  have targetGrade := source.aromaticCanonicalOccurrence_depthGrade target
  omega

/-- The source-canonical occurrence dependency is well founded. -/
theorem aromaticCanonicalDepthDependency_wellFounded
    (source : AuthoritativeChemicalInput) (fuel : Nat) :
    WellFounded (@source.AromaticCanonicalDepthDependency fuel) := by
  refine Subrelation.wf ?_
    (InvImage.wf (fun occurrence : source.AromaticCanonicalOccurrence fuel =>
      occurrence.1.remaining) (Nat.lt_wfRel).2)
  intro dependency target below
  exact source.aromaticCanonicalDepthDependency_remaining_lt below

/-! ## Dependency-restricted chemical fixed point -/

abbrev AromaticCanonicalAuxiliaryLabel := LocalizedTetrahedralRSPseudoDescriptor

def aromaticCanonicalAuxiliaryDescriptor :
    AromaticCanonicalAuxiliaryLabel → DeclarativeCIP.Descriptor
  | .chiral .R => .R
  | .chiral .S => .S
  | .pseudoasymmetric .r => .r
  | .pseudoasymmetric .s => .s

abbrev AromaticCanonicalAuxiliaryState
    (source : AuthoritativeChemicalInput) (fuel : Nat) :=
  source.AromaticCanonicalOccurrence fuel → Option AromaticCanonicalAuxiliaryLabel

abbrev AromaticCanonicalDependencyView
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel) :=
  ∀ dependency : source.AromaticCanonicalOccurrence fuel,
    source.AromaticCanonicalDepthDependency dependency target →
      Option AromaticCanonicalAuxiliaryLabel

def aromaticCanonicalDependencyView
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState fuel)
    (target : source.AromaticCanonicalOccurrence fuel) :
    source.AromaticCanonicalDependencyView target :=
  fun dependency _below => state dependency

abbrev AromaticCanonicalRestrictedEvaluator
    (source : AuthoritativeChemicalInput) (fuel : Nat) :=
  ∀ target : source.AromaticCanonicalOccurrence fuel,
    source.AromaticCanonicalDependencyView target →
      Option AromaticCanonicalAuxiliaryLabel

def aromaticCanonicalExecutableStep
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (evaluator : source.AromaticCanonicalRestrictedEvaluator fuel)
    (state : source.AromaticCanonicalAuxiliaryState fuel)
    (target : source.AromaticCanonicalOccurrence fuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  evaluator target (source.aromaticCanonicalDependencyView state target)

theorem aromaticCanonicalExecutableStep_eq_of_depthAgree
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (evaluator : source.AromaticCanonicalRestrictedEvaluator fuel)
    (left right : source.AromaticCanonicalAuxiliaryState fuel)
    (target : source.AromaticCanonicalOccurrence fuel)
    (agree : ∀ dependency,
      source.AromaticCanonicalDepthDependency dependency target →
        left dependency = right dependency) :
    source.aromaticCanonicalExecutableStep evaluator left target =
      source.aromaticCanonicalExecutableStep evaluator right target := by
  unfold aromaticCanonicalExecutableStep
  apply congrArg (evaluator target)
  funext dependency below
  exact agree dependency below

/-- Concrete chemical semantics for the source-canonical carrier.  The derivation relation is a
separate field; its complete optional-outcome correspondence with execution must be proved. -/
structure AromaticCanonicalRuleSemantics
    (source : AuthoritativeChemicalInput) (fuel : Nat) where
  DeclarativeDerivation :
    source.AromaticCanonicalAuxiliaryState fuel →
      source.AromaticCanonicalOccurrence fuel →
        Option AromaticCanonicalAuxiliaryLabel → Prop
  executableRule : source.AromaticCanonicalRestrictedEvaluator fuel
  derivation_executable_iff : ∀ state target outcome,
    DeclarativeDerivation state target outcome ↔
      executableRule target
        (source.aromaticCanonicalDependencyView state target) = outcome

noncomputable def aromaticCanonicalOccurrenceSystem
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    OccurrenceSystem source.AromaticCanonicalTetrahedralCenter
      (source.AromaticCanonicalOccurrence fuel) AromaticCanonicalAuxiliaryLabel where
  finalOccurrence := source.aromaticCanonicalFinalOccurrence fuel
  descriptorOf := aromaticCanonicalAuxiliaryDescriptor
  DeclarativeDerivation := semantics.DeclarativeDerivation
  executableStep := source.aromaticCanonicalExecutableStep semantics.executableRule

theorem aromaticCanonicalDerivationStepCorrespondence
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    (source.aromaticCanonicalOccurrenceSystem semantics).DerivationStepCorrespondence := by
  intro state target outcome
  exact semantics.derivation_executable_iff state target outcome

theorem aromaticCanonicalEvaluatorLocal
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    (source.aromaticCanonicalOccurrenceSystem semantics).EvaluatorLocalFor
      (@source.AromaticCanonicalDepthDependency fuel) := by
  intro left right target agree
  exact source.aromaticCanonicalExecutableStep_eq_of_depthAgree
    semantics.executableRule left right target agree

/-- Any independently justified source-canonical chemical semantics has exactly one complete
occurrence model. -/
theorem existsUnique_aromaticCanonicalCIPModel
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    ∃! state,
      (source.aromaticCanonicalOccurrenceSystem semantics).CIPModel state :=
  (source.aromaticCanonicalOccurrenceSystem semantics).existsUnique_cipModel_of_wellFounded
    (source.aromaticCanonicalDerivationStepCorrespondence semantics)
    (@source.AromaticCanonicalDepthDependency fuel)
    (source.aromaticCanonicalDepthDependency_wellFounded fuel)
    (source.aromaticCanonicalEvaluatorLocal semantics)

/-- The generic causal closure decodes to the unique source-canonical occurrence model. -/
theorem aromaticCanonicalSchedulerClosure_cipModel
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics fuel) :
    (source.aromaticCanonicalOccurrenceSystem semantics).CIPModel
      (DeclarativeCIP.OccurrenceScheduler.decode
        (source.aromaticCanonicalOccurrenceSystem semantics)
        (@source.AromaticCanonicalDepthDependency fuel)
        (DeclarativeCIP.OccurrenceScheduler.closure
          (source.aromaticCanonicalOccurrenceSystem semantics)
          (@source.AromaticCanonicalDepthDependency fuel))) := by
  exact DeclarativeCIP.OccurrenceScheduler.decode_closure_cipModel
    (source.aromaticCanonicalOccurrenceSystem semantics)
    (source.aromaticCanonicalDerivationStepCorrespondence semantics)
    (@source.AromaticCanonicalDepthDependency fuel)
    (source.aromaticCanonicalDepthDependency_wellFounded fuel)
    (source.aromaticCanonicalEvaluatorLocal semantics)

end AuthoritativeChemicalInput

end TetraStereo.OneCenter
