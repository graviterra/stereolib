import TetraStereo.KernelOnly
import TetraStereo.OneCenter.LocalizedPublicChildEnumeration
import TetraStereo.OneCenter.LocalizedOccurrenceCarrier
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceFixedPoint
import Mathlib.Data.List.Dedup

set_option autoImplicit false

































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The componentwise frame correspondence -/

/-- The four components of a public source-canonical occurrence frame are exactly the four
components of a localized occurrence frame.  This is the forward map of the frame bijection. -/
def localizedPublicFrame (input : CertifiedLocalizedCIPInput)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    input.LocalizedCIPOccurrenceFrame :=
  { root := frame.root
    address := frame.address
    node := frame.node
    remaining := frame.remaining }

/-- Inverse of `localizedPublicFrame`. -/
def publicLocalizedFrame (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input :=
  { root := frame.root
    address := frame.address
    node := frame.node
    remaining := frame.remaining }

@[simp] theorem localizedPublicFrame_root
    (input : CertifiedLocalizedCIPInput)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    (input.localizedPublicFrame frame).root = frame.root := rfl

@[simp] theorem localizedPublicFrame_address
    (input : CertifiedLocalizedCIPInput)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    (input.localizedPublicFrame frame).address = frame.address := rfl

@[simp] theorem localizedPublicFrame_node
    (input : CertifiedLocalizedCIPInput)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    (input.localizedPublicFrame frame).node = frame.node := rfl

@[simp] theorem localizedPublicFrame_remaining
    (input : CertifiedLocalizedCIPInput)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    (input.localizedPublicFrame frame).remaining = frame.remaining := rfl

@[simp] theorem publicLocalizedFrame_root
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.publicLocalizedFrame frame).root = frame.root := rfl

@[simp] theorem publicLocalizedFrame_address
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.publicLocalizedFrame frame).address = frame.address := rfl

@[simp] theorem publicLocalizedFrame_node
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.publicLocalizedFrame frame).node = frame.node := rfl

@[simp] theorem publicLocalizedFrame_remaining
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.publicLocalizedFrame frame).remaining = frame.remaining := rfl

@[simp] theorem localizedPublicFrame_publicLocalizedFrame
    (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedCIPOccurrenceFrame) :
    input.localizedPublicFrame (input.publicLocalizedFrame frame) = frame := by
  cases frame
  rfl

@[simp] theorem publicLocalizedFrame_localizedPublicFrame
    (input : CertifiedLocalizedCIPInput)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    input.publicLocalizedFrame (input.localizedPublicFrame frame) = frame := by
  cases frame
  rfl

/-- The componentwise frame bijection between the two occurrence carriers. -/
def localizedPublicFrameEquiv (input : CertifiedLocalizedCIPInput) :
    AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input ≃
      input.LocalizedCIPOccurrenceFrame where
  toFun := input.localizedPublicFrame
  invFun := input.publicLocalizedFrame
  left_inv := input.publicLocalizedFrame_localizedPublicFrame
  right_inv := input.localizedPublicFrame_publicLocalizedFrame

theorem localizedPublicFrame_injective (input : CertifiedLocalizedCIPInput) :
    Function.Injective input.localizedPublicFrame :=
  (input.localizedPublicFrameEquiv).injective

/-! ## Exact subtree transport -/




theorem map_localizedPublicFrame_aromaticCanonicalOccurrenceSubtree
    (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    ∀ (fuel : Nat) (path : List Nat) (node : OfficialCIPNode input.Atom),
      (input.certified.input.aromaticCanonicalOccurrenceSubtree root fuel path node).map
          input.localizedPublicFrame =
        input.localizedOccurrenceSubtree root fuel path node
  | 0, path, node => rfl
  | fuel + 1, path, node => by
      rw [AuthoritativeChemicalInput.aromaticCanonicalOccurrenceSubtree,
        CertifiedLocalizedCIPInput.localizedOccurrenceSubtree]
      rw [List.map_cons, List.map_flatMap]
      rw [input.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren node]
      have childrenMap :
          (fun child : OfficialCIPNode input.Atom × Nat =>
              (input.certified.input.aromaticCanonicalOccurrenceSubtree root fuel
                (path ++ [child.2]) child.1).map input.localizedPublicFrame) =
            (fun child : OfficialCIPNode input.Atom × Nat =>
              input.localizedOccurrenceSubtree root fuel (path ++ [child.2]) child.1) := by
        funext child
        exact map_localizedPublicFrame_aromaticCanonicalOccurrenceSubtree input root fuel
          (path ++ [child.2]) child.1
      rw [childrenMap]
      rfl

/-- The inverse frame map carries the localized subtree back onto the public subtree. -/
theorem map_publicLocalizedFrame_localizedOccurrenceSubtree
    (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    ∀ (fuel : Nat) (path : List Nat) (node : OfficialCIPNode input.Atom),
      (input.localizedOccurrenceSubtree root fuel path node).map input.publicLocalizedFrame =
        input.certified.input.aromaticCanonicalOccurrenceSubtree root fuel path node
  | 0, path, node => rfl
  | fuel + 1, path, node => by
      have forward :=
        map_localizedPublicFrame_aromaticCanonicalOccurrenceSubtree input root (fuel + 1)
          path node
      have mapped := congrArg (List.map input.publicLocalizedFrame) forward
      have composition : input.publicLocalizedFrame ∘ input.localizedPublicFrame = id := by
        funext frame
        exact input.publicLocalizedFrame_localizedPublicFrame frame
      rw [List.map_map, composition, List.map_id] at mapped
      exact mapped.symm

/-- Per-atom occurrence enumeration: the public atom-rooted family maps exactly onto the
localized atom-rooted family. -/
theorem map_localizedPublicFrame_aromaticCanonicalOccurrencesAtAtom
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.certified.input.aromaticCanonicalOccurrencesAtAtom fuel atom).map
        input.localizedPublicFrame =
      input.localizedOccurrencesAtAtom fuel atom :=
  map_localizedPublicFrame_aromaticCanonicalOccurrenceSubtree input atom (fuel + 1) []
    (OfficialCIPNode.root atom)

/-- Molecule-wide occurrence enumeration: the public `flatMap` over `List.finRange`, followed by
`dedup`, maps exactly onto the localized molecule-wide family.  Injectivity of the frame map is
what allows `dedup` to commute with the mapping. -/
theorem map_localizedPublicFrame_aromaticCanonicalOccurrences
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.certified.input.aromaticCanonicalOccurrences fuel).map input.localizedPublicFrame =
      input.localizedOccurrences fuel := by
  have injective : Function.Injective input.localizedPublicFrame :=
    input.localizedPublicFrame_injective
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrences
    CertifiedLocalizedCIPInput.localizedOccurrences
  rw [(List.dedup_map_of_injective injective _).symm]
  rw [List.map_flatMap]
  rw [show (fun atom : input.Atom =>
        (input.certified.input.aromaticCanonicalOccurrencesAtAtom fuel atom).map
          input.localizedPublicFrame) =
      (fun atom : input.Atom => input.localizedOccurrencesAtAtom fuel atom) from by
    funext atom
    exact input.map_localizedPublicFrame_aromaticCanonicalOccurrencesAtAtom fuel atom]

/-- Membership in the public molecule-wide carrier is equivalent to membership of the mapped
frame in the localized molecule-wide carrier. -/
theorem mem_aromaticCanonicalOccurrences_iff_localizedPublicFrame_mem
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (frame : AuthoritativeChemicalInput.AromaticCanonicalOccurrenceFrame input.certified.input) :
    frame ∈ input.certified.input.aromaticCanonicalOccurrences fuel ↔
      input.localizedPublicFrame frame ∈ input.localizedOccurrences fuel := by
  constructor
  · intro present
    have mapped : input.localizedPublicFrame frame ∈
        (input.certified.input.aromaticCanonicalOccurrences fuel).map
          input.localizedPublicFrame :=
      List.mem_map_of_mem present
    rw [input.map_localizedPublicFrame_aromaticCanonicalOccurrences fuel] at mapped
    exact mapped
  · intro present
    have mapped : input.localizedPublicFrame frame ∈
        (input.certified.input.aromaticCanonicalOccurrences fuel).map
          input.localizedPublicFrame := by
      rw [input.map_localizedPublicFrame_aromaticCanonicalOccurrences fuel]
      exact present
    rcases List.mem_map.mp mapped with ⟨candidate, candidatePresent, candidateEq⟩
    have same : candidate = frame := input.localizedPublicFrame_injective candidateEq
    simpa [same] using candidatePresent

/-! ## The occurrence equivalence -/

/-- **The actual occurrence equivalence** between the public source-canonical carrier and the
localized carrier at a fixed certified input and fuel bound.  It is induced by the componentwise
frame bijection and the molecule-wide mapped-enumeration equality. -/
def localizedPublicOccurrenceEquiv (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.certified.input.AromaticCanonicalOccurrence fuel ≃
      input.LocalizedCIPOccurrence fuel where
  toFun occurrence :=
    ⟨input.localizedPublicFrame occurrence.1,
      (input.mem_aromaticCanonicalOccurrences_iff_localizedPublicFrame_mem fuel
        occurrence.1).mp occurrence.2⟩
  invFun occurrence :=
    ⟨input.publicLocalizedFrame occurrence.1,
      (input.mem_aromaticCanonicalOccurrences_iff_localizedPublicFrame_mem fuel
        (input.publicLocalizedFrame occurrence.1)).mpr (by
          simpa using occurrence.2)⟩
  left_inv occurrence := by
    apply Subtype.ext
    exact input.publicLocalizedFrame_localizedPublicFrame occurrence.1
  right_inv occurrence := by
    apply Subtype.ext
    exact input.localizedPublicFrame_publicLocalizedFrame occurrence.1

@[simp] theorem localizedPublicOccurrenceEquiv_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.certified.input.AromaticCanonicalOccurrence fuel) :
    (input.localizedPublicOccurrenceEquiv fuel occurrence).1.root = occurrence.1.root := rfl

@[simp] theorem localizedPublicOccurrenceEquiv_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.certified.input.AromaticCanonicalOccurrence fuel) :
    (input.localizedPublicOccurrenceEquiv fuel occurrence).1.address = occurrence.1.address := rfl

@[simp] theorem localizedPublicOccurrenceEquiv_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.certified.input.AromaticCanonicalOccurrence fuel) :
    (input.localizedPublicOccurrenceEquiv fuel occurrence).1.node = occurrence.1.node := rfl

@[simp] theorem localizedPublicOccurrenceEquiv_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.certified.input.AromaticCanonicalOccurrence fuel) :
    (input.localizedPublicOccurrenceEquiv fuel occurrence).1.remaining =
      occurrence.1.remaining := rfl

/-- The equivalence is exactly the componentwise frame map on representatives. -/
@[simp] theorem localizedPublicOccurrenceEquiv_val
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.certified.input.AromaticCanonicalOccurrence fuel) :
    (input.localizedPublicOccurrenceEquiv fuel occurrence).1 =
      input.localizedPublicFrame occurrence.1 := rfl

/-- The inverse equivalence is exactly the inverse frame map on representatives. -/
@[simp] theorem localizedPublicOccurrenceEquiv_symm_val
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence).1 =
      input.publicLocalizedFrame occurrence.1 := rfl

/-! ## Dependency transport -/

/-- The strict root-relative depth dependency is transported exactly by the occurrence
equivalence: a public dependency holds precisely when the corresponding localized dependency
holds. -/
theorem aromaticCanonicalDepthDependency_iff_localizedDepthDependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (dependency target : input.certified.input.AromaticCanonicalOccurrence fuel) :
    input.certified.input.AromaticCanonicalDepthDependency dependency target ↔
      input.LocalizedDepthDependency
        (input.localizedPublicOccurrenceEquiv fuel dependency)
        (input.localizedPublicOccurrenceEquiv fuel target) := by
  constructor
  · rintro ⟨sameRoot, deeper⟩
    exact ⟨sameRoot, deeper⟩
  · rintro ⟨sameRoot, deeper⟩
    exact ⟨sameRoot, deeper⟩

/-- The inverse form of the dependency correspondence, stateable directly on localized
occurrences. -/
theorem localizedDepthDependency_iff_aromaticCanonicalDepthDependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (dependency target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedDepthDependency dependency target ↔
      input.certified.input.AromaticCanonicalDepthDependency
        ((input.localizedPublicOccurrenceEquiv fuel).symm dependency)
        ((input.localizedPublicOccurrenceEquiv fuel).symm target) := by
  have transported :=
    input.aromaticCanonicalDepthDependency_iff_localizedDepthDependency
      ((input.localizedPublicOccurrenceEquiv fuel).symm dependency)
      ((input.localizedPublicOccurrenceEquiv fuel).symm target)
  simpa using transported.symm

/-- The distinguished public atom-root occurrence at the empty address. -/
def publicAtomRootOccurrence (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (atom : input.Atom) : input.certified.input.AromaticCanonicalOccurrence fuel :=
  ⟨{ root := atom
     address := []
     node := OfficialCIPNode.root atom
     remaining := fuel + 1 }, by
    apply (input.certified.input.mem_aromaticCanonicalOccurrences_iff fuel _).mpr
    exact AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
      [] (fuel + 1) (OfficialCIPNode.root atom)⟩

@[simp] theorem publicAtomRootOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.publicAtomRootOccurrence fuel atom).1.root = atom := rfl

@[simp] theorem publicAtomRootOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.publicAtomRootOccurrence fuel atom).1.address = [] := rfl

@[simp] theorem publicAtomRootOccurrence_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.publicAtomRootOccurrence fuel atom).1.node = OfficialCIPNode.root atom := rfl

@[simp] theorem publicAtomRootOccurrence_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.publicAtomRootOccurrence fuel atom).1.remaining = fuel + 1 := rfl

/-- The public atom-root occurrence transports to the localized atom-root occurrence of the same
atom: the two carriers agree on the distinguished empty-address coordinate. -/
@[simp] theorem localizedPublicOccurrenceEquiv_publicAtomRootOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    input.localizedPublicOccurrenceEquiv fuel (input.publicAtomRootOccurrence fuel atom) =
      input.localizedAtomRootOccurrence fuel atom := by
  apply Subtype.ext
  rfl

/-! ## Auxiliary-state transport -/

/-- Pull a localized auxiliary state back along the occurrence equivalence: a public occurrence
reads the label of its localized image. -/
def publicStateOfLocalized (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.certified.input.AromaticCanonicalAuxiliaryState fuel :=
  fun occurrence => state (input.localizedPublicOccurrenceEquiv fuel occurrence)

/-- Push a public auxiliary state forward along the occurrence equivalence. -/
def localizedStateOfPublic (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.certified.input.AromaticCanonicalAuxiliaryState fuel) :
    input.LocalizedAuxiliaryState fuel :=
  fun occurrence => state ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence)

@[simp] theorem publicStateOfLocalized_apply
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (occurrence : input.certified.input.AromaticCanonicalOccurrence fuel) :
    input.publicStateOfLocalized fuel state occurrence =
      state (input.localizedPublicOccurrenceEquiv fuel occurrence) := rfl

@[simp] theorem localizedStateOfPublic_apply
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.certified.input.AromaticCanonicalAuxiliaryState fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.localizedStateOfPublic fuel state occurrence =
      state ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence) := rfl

@[simp] theorem localizedStateOfPublic_publicStateOfLocalized
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.localizedStateOfPublic fuel (input.publicStateOfLocalized fuel state) = state := by
  funext occurrence
  simp [localizedStateOfPublic, publicStateOfLocalized]

@[simp] theorem publicStateOfLocalized_localizedStateOfPublic
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.certified.input.AromaticCanonicalAuxiliaryState fuel) :
    input.publicStateOfLocalized fuel (input.localizedStateOfPublic fuel state) = state := by
  funext occurrence
  simp [publicStateOfLocalized, localizedStateOfPublic]

/-- The complete auxiliary-state spaces of the two carriers are equivalent. -/
def localizedPublicStateEquiv (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.certified.input.AromaticCanonicalAuxiliaryState fuel ≃
      input.LocalizedAuxiliaryState fuel where
  toFun := input.localizedStateOfPublic fuel
  invFun := input.publicStateOfLocalized fuel
  left_inv := input.publicStateOfLocalized_localizedStateOfPublic fuel
  right_inv := input.localizedStateOfPublic_publicStateOfLocalized fuel

/-! ## Dependency-view and restricted-evaluator transport -/

/-- Transport a localized dependency-restricted evaluator to the public carrier.  The public
target is evaluated at its localized image; each localized dependency the evaluator may read is
offered to the public view at its public preimage, with the dependency proof transported by
`aromaticCanonicalDepthDependency_iff_localizedDepthDependency`. -/
def publicRestrictedEvaluatorOfLocalized (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (evaluator : input.LocalizedRestrictedEvaluator fuel) :
    input.certified.input.AromaticCanonicalRestrictedEvaluator fuel :=
  fun target view =>
    evaluator (input.localizedPublicOccurrenceEquiv fuel target)
      (fun dependency below =>
        view ((input.localizedPublicOccurrenceEquiv fuel).symm dependency)
          ((input.aromaticCanonicalDepthDependency_iff_localizedDepthDependency
            ((input.localizedPublicOccurrenceEquiv fuel).symm dependency) target).mpr
            (by simpa using below)))

/-- **Dependency-view transport.**  The transported public evaluator, applied to the public view of
a public state, reads exactly the localized dependency view of the corresponding localized state
at the corresponding occurrence.  Only dependency coordinates are ever consulted. -/
theorem publicRestrictedEvaluatorOfLocalized_apply_dependencyView
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (state : input.certified.input.AromaticCanonicalAuxiliaryState fuel)
    (target : input.certified.input.AromaticCanonicalOccurrence fuel) :
    input.publicRestrictedEvaluatorOfLocalized fuel evaluator target
        (input.certified.input.aromaticCanonicalDependencyView state target) =
      evaluator (input.localizedPublicOccurrenceEquiv fuel target)
        (input.localizedDependencyView (input.localizedStateOfPublic fuel state)
          (input.localizedPublicOccurrenceEquiv fuel target)) := by
  unfold publicRestrictedEvaluatorOfLocalized
  refine congrArg (evaluator (input.localizedPublicOccurrenceEquiv fuel target)) ?_
  funext dependency below
  unfold AuthoritativeChemicalInput.aromaticCanonicalDependencyView
    CertifiedLocalizedCIPInput.localizedDependencyView
    CertifiedLocalizedCIPInput.localizedStateOfPublic
  rfl

/-- **Executable-step transport.**  Public executable evaluation with the transported evaluator
and the transported state equals localized executable evaluation at the image occurrence. -/
theorem aromaticCanonicalExecutableStep_eq_localizedExecutableStep
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (evaluator : input.LocalizedRestrictedEvaluator fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.certified.input.AromaticCanonicalOccurrence fuel) :
    input.certified.input.aromaticCanonicalExecutableStep
        (input.publicRestrictedEvaluatorOfLocalized fuel evaluator)
        (input.publicStateOfLocalized fuel state) target =
      input.localizedExecutableStep evaluator state
        (input.localizedPublicOccurrenceEquiv fuel target) := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalExecutableStep
    CertifiedLocalizedCIPInput.localizedExecutableStep
  rw [input.publicRestrictedEvaluatorOfLocalized_apply_dependencyView]
  rw [input.localizedStateOfPublic_publicStateOfLocalized]

/-! ## Rule-semantics and fixed-point transport -/

/-- Transport a localized occurrence semantics to the public source-canonical carrier.  The
declarative rules are reindexed along the occurrence equivalence and the executable member is the
transported restricted evaluator.  Crucially, the mandatory correspondence field is *derived* from
the localized correspondence plus the step-transport theorem; it is not assumed. -/
def publicRuleSemanticsOfLocalized (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel) :
    input.certified.input.AromaticCanonicalRuleSemantics fuel where
  DeclarativeDerivation := fun state target outcome =>
    semantics.DeclarativeDerivation (input.localizedStateOfPublic fuel state)
      (input.localizedPublicOccurrenceEquiv fuel target) outcome
  executableRule := input.publicRestrictedEvaluatorOfLocalized fuel semantics.executableRule
  derivation_executable_iff := by
    intro state target outcome
    rw [semantics.derivation_executable_iff (input.localizedStateOfPublic fuel state)
      (input.localizedPublicOccurrenceEquiv fuel target) outcome]
    rw [input.publicRestrictedEvaluatorOfLocalized_apply_dependencyView]

/-- The transported public declarative rules are exactly the localized rules read at the image
occurrence. -/
@[simp] theorem publicRuleSemanticsOfLocalized_DeclarativeDerivation
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.certified.input.AromaticCanonicalAuxiliaryState fuel)
    (target : input.certified.input.AromaticCanonicalOccurrence fuel)
    (outcome : Option AuthoritativeChemicalInput.AromaticCanonicalAuxiliaryLabel) :
    (input.publicRuleSemanticsOfLocalized semantics).DeclarativeDerivation state target outcome ↔
      semantics.DeclarativeDerivation (input.localizedStateOfPublic fuel state)
        (input.localizedPublicOccurrenceEquiv fuel target) outcome :=
  Iff.rfl

/-- A complete localized model transports to a complete model of the transported public
semantics. -/
theorem cipModel_public_of_localized
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state) :
    (input.certified.input.aromaticCanonicalOccurrenceSystem
        (input.publicRuleSemanticsOfLocalized semantics)).CIPModel
      (input.publicStateOfLocalized fuel state) := by
  intro target
  change semantics.DeclarativeDerivation
    (input.localizedStateOfPublic fuel (input.publicStateOfLocalized fuel state))
    (input.localizedPublicOccurrenceEquiv fuel target)
    (input.publicStateOfLocalized fuel state target)
  rw [input.localizedStateOfPublic_publicStateOfLocalized]
  exact model (input.localizedPublicOccurrenceEquiv fuel target)

/-- Conversely, a complete public model of the transported semantics is a complete localized
model of the original semantics. -/
theorem cipModel_localized_of_public
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.certified.input.aromaticCanonicalOccurrenceSystem
        (input.publicRuleSemanticsOfLocalized semantics)).CIPModel
      (input.publicStateOfLocalized fuel state)) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state := by
  intro occurrence
  have hat := model ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence)
  change semantics.DeclarativeDerivation
    (input.localizedStateOfPublic fuel (input.publicStateOfLocalized fuel state))
    (input.localizedPublicOccurrenceEquiv fuel
      ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence))
    (input.publicStateOfLocalized fuel state
      ((input.localizedPublicOccurrenceEquiv fuel).symm occurrence)) at hat
  rw [input.localizedStateOfPublic_publicStateOfLocalized] at hat
  simpa using hat

/-- **Complete-model correspondence.**  The fixed points of the two carriers coincide under the
occurrence equivalence and the induced state equivalence: a localized state is a model of the
localized semantics exactly when its public image is a model of the transported public semantics. -/
theorem cipModel_iff_transport
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (state : input.LocalizedAuxiliaryState fuel) :
    (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state ↔
      (input.certified.input.aromaticCanonicalOccurrenceSystem
        (input.publicRuleSemanticsOfLocalized semantics)).CIPModel
        (input.publicStateOfLocalized fuel state) :=
  ⟨input.cipModel_public_of_localized semantics state,
    input.cipModel_localized_of_public semantics state⟩

/-- **Existence and uniqueness transfer.**  If the localized semantics has exactly one complete
occurrence model, then the transported public semantics has exactly one complete occurrence model,
obtained as the transported state.  This is uniqueness of the *transported* semantics; it does not
identify the transported evaluator with any independently written public Rules-3--6 evaluator. -/
theorem existsUnique_publicCIPModel_of_localized
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (semantics : input.LocalizedAuxiliaryRuleSemantics fuel)
    (unique : ∃! state,
      (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel state) :
    ∃! state,
      (input.certified.input.aromaticCanonicalOccurrenceSystem
        (input.publicRuleSemanticsOfLocalized semantics)).CIPModel state := by
  obtain ⟨witness, witnessModel, witnessUnique⟩ := unique
  refine ⟨input.publicStateOfLocalized fuel witness,
    input.cipModel_public_of_localized semantics witness witnessModel, ?_⟩
  intro candidate candidateModel
  have candidateLocalized :
      (input.localizedAuxiliaryOccurrenceSystem semantics).CIPModel
        (input.localizedStateOfPublic fuel candidate) := by
    apply input.cipModel_localized_of_public semantics
      (input.localizedStateOfPublic fuel candidate)
    rw [input.publicStateOfLocalized_localizedStateOfPublic]
    exact candidateModel
  have sameLocalized := witnessUnique _ candidateLocalized
  rw [← sameLocalized]
  exact (input.publicStateOfLocalized_localizedStateOfPublic fuel candidate).symm

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicFrame_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicFrame_address
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicFrame_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicFrame_remaining
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicLocalizedFrame_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicLocalizedFrame_address
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicLocalizedFrame_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicLocalizedFrame_remaining
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicFrame_publicLocalizedFrame
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicLocalizedFrame_localizedPublicFrame
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicFrame_injective
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.map_localizedPublicFrame_aromaticCanonicalOccurrenceSubtree
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.map_publicLocalizedFrame_localizedOccurrenceSubtree
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.map_localizedPublicFrame_aromaticCanonicalOccurrencesAtAtom
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.map_localizedPublicFrame_aromaticCanonicalOccurrences
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_aromaticCanonicalOccurrences_iff_localizedPublicFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_address
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_remaining
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_val
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_symm_val
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.aromaticCanonicalDepthDependency_iff_localizedDepthDependency
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDepthDependency_iff_aromaticCanonicalDepthDependency
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicAtomRootOccurrence_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicAtomRootOccurrence_address
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicAtomRootOccurrence_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicAtomRootOccurrence_remaining
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPublicOccurrenceEquiv_publicAtomRootOccurrence
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedStateOfPublic_publicStateOfLocalized
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicStateOfLocalized_localizedStateOfPublic
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicRestrictedEvaluatorOfLocalized_apply_dependencyView
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.aromaticCanonicalExecutableStep_eq_localizedExecutableStep
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicRuleSemanticsOfLocalized_DeclarativeDerivation
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cipModel_public_of_localized
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cipModel_localized_of_public
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cipModel_iff_transport
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.publicStateOfLocalized_apply
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedStateOfPublic_apply
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.existsUnique_publicCIPModel_of_localized
