import TetraStereo.OneCenter.LocalizedRule3Occurrence
import TetraStereo.OneCenter.LocalizedRerootRuleMajorKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Constitution-ranked reroot Rule 3 spatial observations

A Rule-3 ligand reading must be unary and must follow the hierarchy order already established by
Rules 1a--2.  A complete reroot rule-major key already carries exactly that ordered addressed
source tree.  This module scans those source nodes fail-closed and records the resulting finite
geometry-priority sequence behind the constitutional key.

The key is explicitly named `Uncancelled`: cyclic/shared physical-unit cancellation and coupled
geometry sequencing are not yet imposed.  Consequently this module proves construction soundness
and comparator lawfulness, but it is not yet wired into the final occurrence descriptor.
-/

namespace CertifiedLocalizedCIPInput

/-- Molecule-backed Rule-3 spatial result at one provenance node. -/
structure LocalizedRule3SpatialNodeResult
    (input : CertifiedLocalizedCIPInput) where
  left : input.Atom
  right : input.Atom
  unit : input.LocalizedRule3SpatialUnitResult
  deriving DecidableEq, Repr

/-- A provenance node is a real child end of a physical order-two edge. -/
def LocalizedRule3NodeHasDoubleBondEdge
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    ∃ current parent,
      node.current? = some current ∧ node.parent? = some parent ∧
        input.moleculeGraph.bond parent current = 2

/-- Independent positive meaning of a spatial Rule-3 reading at one provenance node. -/
def DeclarativeLocalizedRule3SpatialNode
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    (result : input.LocalizedRule3SpatialNodeResult) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    node.current? = some result.right ∧ node.parent? = some result.left ∧
    input.moleculeGraph.bond result.left result.right = 2 ∧
    input.DeclarativeLocalizedRule3SpatialUnit result.left result.right result.unit

/-- Tri-state node reading: structural nonunit, justified unit, or unresolved genuine unit. -/
noncomputable def localizedRule3SpatialNode?
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  if node.provenance = OfficialCIPNodeProvenance.realAtom then
    match node.current?, node.parent? with
    | some current, some parent =>
        if input.moleculeGraph.bond parent current = 2 then
          match input.localizedRule3SpatialUnit? parent current with
          | none => none
          | some unit => some (some { left := parent, right := current, unit := unit })
        else some none
    | _, _ => some none
  else some none

theorem localizedRule3SpatialNode?_sound
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (result : input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3SpatialNode? node = some (some result)) :
    input.DeclarativeLocalizedRule3SpatialNode node result := by
  unfold localizedRule3SpatialNode? at computed
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real] at computed
    cases currentComputed : node.current? with
    | none => simp [currentComputed] at computed
    | some current =>
        cases parentComputed : node.parent? with
        | none => simp [currentComputed, parentComputed] at computed
        | some parent =>
            by_cases doubleBond : input.moleculeGraph.bond parent current = 2
            · rw [currentComputed, parentComputed] at computed
              change (if input.moleculeGraph.bond parent current = 2 then
                  match input.localizedRule3SpatialUnit? parent current with
                  | none => none
                  | some unit => some (some
                      { left := parent, right := current, unit := unit })
                else some none) = some (some result) at computed
              rw [if_pos doubleBond] at computed
              cases unitComputed : input.localizedRule3SpatialUnit? parent current with
              | none => simp [unitComputed] at computed
              | some unit =>
                  simp [unitComputed] at computed
                  subst result
                  exact ⟨real, currentComputed, parentComputed, doubleBond,
                    input.localizedRule3SpatialUnit?_sound parent current unit unitComputed⟩
            · simp [currentComputed, parentComputed, doubleBond] at computed
  · simp [real] at computed

theorem localizedRule3SpatialNode?_eq_some_none_implies_not_edge
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (computed : input.localizedRule3SpatialNode? node = some none) :
    ¬ input.LocalizedRule3NodeHasDoubleBondEdge node := by
  rintro ⟨real, current, parent, currentComputed, parentComputed, doubleBond⟩
  unfold localizedRule3SpatialNode? at computed
  rw [if_pos real, currentComputed, parentComputed] at computed
  change (if input.moleculeGraph.bond parent current = 2 then
      match input.localizedRule3SpatialUnit? parent current with
      | none => none
      | some unit => some (some
          ({ left := parent, right := current, unit := unit } :
            input.LocalizedRule3SpatialNodeResult))
    else some none) = some none at computed
  rw [if_pos doubleBond] at computed
  cases unitComputed : input.localizedRule3SpatialUnit? parent current <;>
    simp [unitComputed] at computed

/-- Fail-closed node scan in the exact order supplied by the constitutional source tree. -/
noncomputable def localizedRule3SpatialNodeScan?
    (input : CertifiedLocalizedCIPInput) :
    List (OfficialCIPNode input.Atom) →
      Option (List input.LocalizedRule3SpatialNodeResult)
  | [] => some []
  | node :: nodes =>
      match input.localizedRule3SpatialNode? node with
      | none => none
      | some none => input.localizedRule3SpatialNodeScan? nodes
      | some (some result) => do
          let tail ← input.localizedRule3SpatialNodeScan? nodes
          some (result :: tail)

inductive DeclarativeLocalizedRule3SpatialNodeScan
    (input : CertifiedLocalizedCIPInput) :
    List (OfficialCIPNode input.Atom) →
      List input.LocalizedRule3SpatialNodeResult → Prop
  | nil : input.DeclarativeLocalizedRule3SpatialNodeScan [] []
  | skip {node nodes results}
      (notUnit : ¬ input.LocalizedRule3NodeHasDoubleBondEdge node)
      (tail : input.DeclarativeLocalizedRule3SpatialNodeScan nodes results) :
      input.DeclarativeLocalizedRule3SpatialNodeScan (node :: nodes) results
  | keep {node nodes result results}
      (unit : input.DeclarativeLocalizedRule3SpatialNode node result)
      (tail : input.DeclarativeLocalizedRule3SpatialNodeScan nodes results) :
      input.DeclarativeLocalizedRule3SpatialNodeScan
        (node :: nodes) (result :: results)

theorem localizedRule3SpatialNodeScan?_sound
    (input : CertifiedLocalizedCIPInput) :
    ∀ (nodes : List (OfficialCIPNode input.Atom))
      (results : List input.LocalizedRule3SpatialNodeResult),
      input.localizedRule3SpatialNodeScan? nodes = some results →
        input.DeclarativeLocalizedRule3SpatialNodeScan nodes results
  | [], results, computed => by
      simp [localizedRule3SpatialNodeScan?] at computed
      subst results
      exact DeclarativeLocalizedRule3SpatialNodeScan.nil
  | node :: nodes, results, computed => by
      unfold localizedRule3SpatialNodeScan? at computed
      cases unitComputed : input.localizedRule3SpatialNode? node with
      | none => simp [unitComputed] at computed
      | some optionalUnit =>
          cases optionalUnit with
          | none =>
              simp only [unitComputed] at computed
              exact DeclarativeLocalizedRule3SpatialNodeScan.skip
                (input.localizedRule3SpatialNode?_eq_some_none_implies_not_edge
                  node unitComputed)
                (input.localizedRule3SpatialNodeScan?_sound nodes results computed)
          | some result =>
              cases tailComputed : input.localizedRule3SpatialNodeScan? nodes with
              | none => simp [unitComputed, tailComputed] at computed
              | some tail =>
                  simp [unitComputed, tailComputed] at computed
                  subst results
                  exact DeclarativeLocalizedRule3SpatialNodeScan.keep
                    (input.localizedRule3SpatialNode?_sound node result unitComputed)
                    (input.localizedRule3SpatialNodeScan?_sound nodes tail tailComputed)

/-- Flatten the already sphere-major, parent-ranked constitutional source layers without changing
their order. -/
def localizedRerootRule3SourceNodes
    {input : CertifiedLocalizedCIPInput}
    (constitutional : OfficialRuleMajorKey input.Atom) :
    List (OfficialCIPNode input.Atom) :=
  constitutional.sourceNodes.flatten.map Prod.snd

/-- Unary constitutional-plus-Rule-3 data before shared/cyclic physical-unit cancellation. -/
structure LocalizedRerootUncancelledRule3SpatialKey
    (input : CertifiedLocalizedCIPInput) where
  constitutional : OfficialRuleMajorKey input.Atom
  observations : List input.LocalizedRule3SpatialNodeResult
  signature : List Nat

/-- Compile the complete reroot constitution, then scan its hierarchy-ordered provenance nodes.
Any unresolved genuine double bond refuses the whole key. -/
noncomputable def buildLocalizedRerootUncancelledRule3SpatialKey?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootUncancelledRule3SpatialKey := do
  let constitutional ← input.buildLocalizedRerootRuleMajorKey? fuel cursor
  let observations ← input.localizedRule3SpatialNodeScan?
    (localizedRerootRule3SourceNodes constitutional)
  some
    { constitutional := constitutional
      observations := observations
      signature := observations.map fun observation => observation.unit.geometry.priority }

/-- Independent construction relation for the uncancelled unary key. -/
def DeclarativeLocalizedRerootUncancelledRule3SpatialKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootUncancelledRule3SpatialKey) : Prop :=
  input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional ∧
    input.DeclarativeLocalizedRule3SpatialNodeScan
      (localizedRerootRule3SourceNodes key.constitutional) key.observations ∧
    key.signature = key.observations.map fun observation =>
      observation.unit.geometry.priority

/-- Successful key construction has a complete constitutional reroot derivation and accounts for
every provenance node in its fail-closed Rule-3 scan. -/
theorem buildLocalizedRerootUncancelledRule3SpatialKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootUncancelledRule3SpatialKey)
    (computed : input.buildLocalizedRerootUncancelledRule3SpatialKey?
      fuel cursor = some key) :
    input.DeclarativeLocalizedRerootUncancelledRule3SpatialKey fuel cursor key := by
  unfold buildLocalizedRerootUncancelledRule3SpatialKey? at computed
  cases constitutionalComputed : input.buildLocalizedRerootRuleMajorKey? fuel cursor with
  | none => simp [constitutionalComputed] at computed
  | some constitutional =>
      cases observationsComputed : input.localizedRule3SpatialNodeScan?
          (localizedRerootRule3SourceNodes constitutional) with
      | none => simp [constitutionalComputed, observationsComputed] at computed
      | some observations =>
          simp [constitutionalComputed, observationsComputed] at computed
          subst key
          exact ⟨input.buildLocalizedRerootRuleMajorKey?_sound
              fuel cursor constitutional constitutionalComputed,
            input.localizedRule3SpatialNodeScan?_sound
              (localizedRerootRule3SourceNodes constitutional)
              observations observationsComputed,
            rfl⟩

/-- Rules 1a--2 decide first; only their complete tie exposes the unary Rule-3 signature. -/
def compareLocalizedRerootUncancelledRule3SpatialKeys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootUncancelledRule3SpatialKey →
      input.LocalizedRerootUncancelledRule3SpatialKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
    (Ordering.byKey (fun key => key.signature)
      (List.compareLex OfficialRuleMajorKey.compareNat))

/-- The constitutional-plus-signature product is a lawful oriented transitive comparator. -/
theorem compareLocalizedRerootUncancelledRule3SpatialKeys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootUncancelledRule3SpatialKeys := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRerootUncancelledRule3SpatialKeys
  infer_instance

@[simp] theorem compareLocalizedRerootUncancelledRule3SpatialKeys_of_constitutional_gt
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootUncancelledRule3SpatialKey)
    (strict : OfficialRuleMajorKey.compare left.constitutional right.constitutional =
      Ordering.gt) :
    input.compareLocalizedRerootUncancelledRule3SpatialKeys left right = Ordering.gt := by
  simp [compareLocalizedRerootUncancelledRule3SpatialKeys, compareLex, strict,
    Ordering.byKey]

@[simp] theorem compareLocalizedRerootUncancelledRule3SpatialKeys_of_constitutional_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootUncancelledRule3SpatialKey)
    (tied : OfficialRuleMajorKey.compare left.constitutional right.constitutional =
      Ordering.eq) :
    input.compareLocalizedRerootUncancelledRule3SpatialKeys left right =
      List.compareLex OfficialRuleMajorKey.compareNat left.signature right.signature := by
  simp [compareLocalizedRerootUncancelledRule3SpatialKeys, compareLex, tied,
    Ordering.byKey]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
