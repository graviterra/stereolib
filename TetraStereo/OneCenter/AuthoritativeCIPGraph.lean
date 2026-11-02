import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Direct all-element bridge to the constitutional CIP graph

`AuthoritativeChemicalInput` deliberately represents more chemistry than the present pair-bond
`MoleculeGraph`: radicals, aromatic/delocalized systems, coordination and multicentre interactions
all require source-backed CIP normalization before they can be projected to that graph.  This
module identifies the exact closed-shell, explicitly localized covalent subdomain on which no such
projection choice is required.

The bridge is direct.  In particular it does not translate through the parser's small `Element`
enumeration, so every atomic number represented by `PeriodicElement` reaches `MoleculeGraph`
unchanged.  Inputs outside this subdomain are rejected rather than silently losing chemical
information.
-/

/-- Orientation-independent identity of a semantic pair bond. -/
def semanticEdgeKey (left right : ℕ) : ℕ × ℕ :=
  (min left right, max left right)

@[simp] theorem semanticEdgeKey_comm (left right : ℕ) :
    semanticEdgeKey left right = semanticEdgeKey right left := by
  simp [semanticEdgeKey, Nat.min_comm, Nat.max_comm]

namespace SemanticAtom

/-- Atom state that can enter the present localized pair-bond graph without discarding radical or
aromatic-input information.  Charge and isotope state are retained by `MoleculeGraph`. -/
def ExplicitLocalizedClosedShell (atom : SemanticAtom) : Prop :=
  atom.unpairedElectrons = 0 ∧ atom.aromaticInput = false

def explicitLocalizedClosedShell? (atom : SemanticAtom) : Bool :=
  decide (atom.unpairedElectrons = 0) && decide (atom.aromaticInput = false)

@[simp] theorem explicitLocalizedClosedShell?_eq_true_iff (atom : SemanticAtom) :
    atom.explicitLocalizedClosedShell? = true ↔ atom.ExplicitLocalizedClosedShell := by
  simp [explicitLocalizedClosedShell?, ExplicitLocalizedClosedShell]

/-- Exact Rule-2 datum for this atom spelling, taken from the frozen standard-atomic-weight and
AME nuclide-mass sources.  The integer is an exact source decimal scaled by `10^12`. -/
def rule2MassPico? (atom : SemanticAtom) : Option CIPRule2MassData.MassPico :=
  CIPRule2MassData.rule2MassPico? atom.element.atomicNumber atom.isotopeMassNumber?

/-- An atom has a Rule-2 value precisely when its ordinary element or explicit nuclide occurs in
the frozen authority data. -/
def Rule2MassKnown (atom : SemanticAtom) : Prop :=
  ∃ mass, atom.rule2MassPico? = some mass

def rule2MassKnown? (atom : SemanticAtom) : Bool := atom.rule2MassPico?.isSome

@[simp] theorem rule2MassKnown?_eq_true_iff (atom : SemanticAtom) :
    atom.rule2MassKnown? = true ↔ atom.Rule2MassKnown := by
  exact Option.isSome_iff_exists

end SemanticAtom

namespace SemanticInteraction

/-- A positive-order, explicitly localized, two-atom covalent bond. -/
def IsLocalizedCovalentPair (interaction : SemanticInteraction) : Prop :=
  ∃ left right order,
    interaction.participants = [left, right] ∧
      interaction.kind = .covalent order ∧ 0 < order

/-- Extract the unordered endpoints and positive order of an explicitly localized covalent pair. -/
def localizedCovalentRecord? (interaction : SemanticInteraction) :
    Option ((ℕ × ℕ) × ℕ) :=
  match interaction.participants, interaction.kind with
  | [left, right], .covalent order =>
      if 0 < order then some (semanticEdgeKey left right, order) else none
  | _, _ => none

@[simp] theorem localizedCovalentRecord?_isSome (interaction : SemanticInteraction) :
    interaction.localizedCovalentRecord?.isSome = true ↔
      interaction.IsLocalizedCovalentPair := by
  cases participantsObserved : interaction.participants with
  | nil => simp [localizedCovalentRecord?, IsLocalizedCovalentPair, participantsObserved]
  | cons left rest =>
      cases rest with
      | nil => simp [localizedCovalentRecord?, IsLocalizedCovalentPair, participantsObserved]
      | cons right tail =>
          cases tail with
          | nil =>
              cases kindObserved : interaction.kind <;>
                simp [localizedCovalentRecord?, IsLocalizedCovalentPair,
                  participantsObserved, kindObserved]
          | cons third tail =>
              simp [localizedCovalentRecord?, IsLocalizedCovalentPair, participantsObserved]

theorem localizedCovalentRecord?_eq_some_order_positive
    (interaction : SemanticInteraction) (key : ℕ × ℕ) (order : ℕ)
    (observed : interaction.localizedCovalentRecord? = some (key, order)) :
    0 < order := by
  cases participantsObserved : interaction.participants with
  | nil => simp [localizedCovalentRecord?, participantsObserved] at observed
  | cons left rest =>
      cases rest with
      | nil => simp [localizedCovalentRecord?, participantsObserved] at observed
      | cons right tail =>
          cases tail with
          | nil =>
              cases kindObserved : interaction.kind <;>
                simp [localizedCovalentRecord?, participantsObserved, kindObserved] at observed
              omega
          | cons third tail =>
              simp [localizedCovalentRecord?, participantsObserved] at observed

/-- Contribution of one semantic interaction to the localized bond order at an unordered pair.
Unsupported interaction kinds contribute zero; the readiness certificate below proves that they
cannot occur on the admitted path. -/
def localizedBondOrderFor (interaction : SemanticInteraction) (left right : ℕ) : ℕ :=
  match interaction.localizedCovalentRecord? with
  | some (key, order) => if key = semanticEdgeKey left right then order else 0
  | none => 0

@[simp] theorem localizedBondOrderFor_comm (interaction : SemanticInteraction) (left right : ℕ) :
    interaction.localizedBondOrderFor left right =
      interaction.localizedBondOrderFor right left := by
  simp [localizedBondOrderFor, semanticEdgeKey_comm]

end SemanticInteraction

namespace SemanticMolecule

/-- Every atom is an explicitly localized closed-shell atom. -/
def ExplicitLocalizedClosedShellAtoms (molecule : SemanticMolecule) : Prop :=
  ∀ atom, atom ∈ molecule.atoms → atom.ExplicitLocalizedClosedShell

/-- Every atom has an authoritative ordinary-element or explicit-nuclide Rule-2 mass datum. -/
def AllRule2MassesKnown (molecule : SemanticMolecule) : Prop :=
  ∀ atom, atom ∈ molecule.atoms → atom.Rule2MassKnown

/-- Every interaction is already a positive-order localized pair bond. -/
def LocalizedCovalentPairsOnly (molecule : SemanticMolecule) : Prop :=
  ∀ interaction, interaction ∈ molecule.interactions →
    interaction.IsLocalizedCovalentPair

/-- Extracted localized pair-bond records. On `LocalizedCovalentPairsOnly`, the `filterMap` drops
nothing. -/
def localizedCovalentRecords (molecule : SemanticMolecule) : List ((ℕ × ℕ) × ℕ) :=
  molecule.interactions.filterMap SemanticInteraction.localizedCovalentRecord?

/-- Extracted unordered bond keys. -/
def localizedCovalentKeys (molecule : SemanticMolecule) : List (ℕ × ℕ) :=
  molecule.localizedCovalentRecords.map Prod.fst

theorem localizedCovalentRecord_order_positive
    (molecule : SemanticMolecule) (key : ℕ × ℕ) (order : ℕ)
    (present : (key, order) ∈ molecule.localizedCovalentRecords) : 0 < order := by
  rw [localizedCovalentRecords, List.mem_filterMap] at present
  obtain ⟨interaction, interactionPresent, observed⟩ := present
  exact SemanticInteraction.localizedCovalentRecord?_eq_some_order_positive
    interaction key order observed

/-- No two records denote the same constitutional pair, regardless of endpoint orientation. -/
def LocalizedCovalentRecordsUnique (molecule : SemanticMolecule) : Prop :=
  molecule.localizedCovalentKeys.Nodup

/-- Exact current domain of the direct semantic-molecule-to-`MoleculeGraph` projection.

This is intentionally a normalization readiness predicate, not a claim of chemical admissibility.
Radicals, aromatic/delocalized bonds, coordinate and multicentre chemistry need additional
normative normalization semantics and therefore fail this gate. -/
def LocalizedCIPGraphReady (molecule : SemanticMolecule) : Prop :=
  molecule.StructurallyWellFormed ∧
    molecule.ExplicitLocalizedClosedShellAtoms ∧
      molecule.AllRule2MassesKnown ∧
        molecule.LocalizedCovalentPairsOnly ∧ molecule.LocalizedCovalentRecordsUnique

def explicitLocalizedClosedShellAtoms? (molecule : SemanticMolecule) : Bool :=
  molecule.atoms.all SemanticAtom.explicitLocalizedClosedShell?

def allRule2MassesKnown? (molecule : SemanticMolecule) : Bool :=
  molecule.atoms.all SemanticAtom.rule2MassKnown?

def localizedCovalentPairsOnly? (molecule : SemanticMolecule) : Bool :=
  molecule.interactions.all fun interaction =>
    interaction.localizedCovalentRecord?.isSome

def localizedCovalentRecordsUnique? (molecule : SemanticMolecule) : Bool :=
  decide molecule.localizedCovalentKeys.Nodup

def localizedCIPGraphReady? (molecule : SemanticMolecule) : Bool :=
  molecule.structurallyWellFormed? &&
    molecule.explicitLocalizedClosedShellAtoms? &&
      molecule.allRule2MassesKnown? &&
        molecule.localizedCovalentPairsOnly? && molecule.localizedCovalentRecordsUnique?

@[simp] theorem explicitLocalizedClosedShellAtoms?_eq_true_iff
    (molecule : SemanticMolecule) :
    molecule.explicitLocalizedClosedShellAtoms? = true ↔
      molecule.ExplicitLocalizedClosedShellAtoms := by
  simp [explicitLocalizedClosedShellAtoms?, ExplicitLocalizedClosedShellAtoms]

@[simp] theorem allRule2MassesKnown?_eq_true_iff (molecule : SemanticMolecule) :
    molecule.allRule2MassesKnown? = true ↔ molecule.AllRule2MassesKnown := by
  simp [allRule2MassesKnown?, AllRule2MassesKnown]

@[simp] theorem localizedCovalentPairsOnly?_eq_true_iff (molecule : SemanticMolecule) :
    molecule.localizedCovalentPairsOnly? = true ↔
      molecule.LocalizedCovalentPairsOnly := by
  simp [localizedCovalentPairsOnly?, LocalizedCovalentPairsOnly]

@[simp] theorem localizedCovalentRecordsUnique?_eq_true_iff (molecule : SemanticMolecule) :
    molecule.localizedCovalentRecordsUnique? = true ↔
      molecule.LocalizedCovalentRecordsUnique := by
  simp [localizedCovalentRecordsUnique?, LocalizedCovalentRecordsUnique]

@[simp] theorem localizedCIPGraphReady?_eq_true_iff (molecule : SemanticMolecule) :
    molecule.localizedCIPGraphReady? = true ↔ molecule.LocalizedCIPGraphReady := by
  simp [localizedCIPGraphReady?, LocalizedCIPGraphReady, and_assoc]

/-- Lookup a localized order by unordered edge key. -/
def localizedBondOrderAtKey : List ((ℕ × ℕ) × ℕ) → (ℕ × ℕ) → ℕ
  | [], _ => 0
  | record :: rest, key =>
      if record.1 = key then record.2 else localizedBondOrderAtKey rest key

/-- A unique extracted record is recovered with exactly its stated order. -/
theorem localizedBondOrderAtKey_eq_of_mem_unique
    (records : List ((ℕ × ℕ) × ℕ)) (key : ℕ × ℕ) (order : ℕ)
    (unique : (records.map Prod.fst).Nodup)
    (present : (key, order) ∈ records) :
    localizedBondOrderAtKey records key = order := by
  induction records with
  | nil => simp at present
  | cons head tail inductionHypothesis =>
      have headFresh : head.1 ∉ tail.map Prod.fst := by
        simpa using (List.nodup_cons.mp unique).1
      have tailUnique : (tail.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp unique).2
      rcases List.mem_cons.mp present with equality | tailPresent
      · subst head
        simp [localizedBondOrderAtKey]
      · have headKeyNe : head.1 ≠ key := by
          intro sameKey
          apply headFresh
          rw [List.mem_map]
          exact ⟨(key, order), tailPresent, by simp [sameKey]⟩
        simp [localizedBondOrderAtKey, headKeyNe,
          inductionHypothesis tailUnique tailPresent]

/-- A key absent from the extracted record list has bond order zero. -/
theorem localizedBondOrderAtKey_eq_zero_of_not_mem
    (records : List ((ℕ × ℕ) × ℕ)) (key : ℕ × ℕ)
    (absent : key ∉ records.map Prod.fst) :
    localizedBondOrderAtKey records key = 0 := by
  induction records with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headNe : head.1 ≠ key := by
        intro equality
        apply absent
        simp [equality]
      have tailAbsent : key ∉ tail.map Prod.fst := by
        intro present
        exact absent (by simp [present])
      simp [localizedBondOrderAtKey, headNe, inductionHypothesis tailAbsent]

/-- Symmetric localized order obtained by exact lookup in the explicit pair records. -/
def localizedBondOrder (molecule : SemanticMolecule) (left right : ℕ) : ℕ :=
  if left = right then 0
  else localizedBondOrderAtKey molecule.localizedCovalentRecords
    (semanticEdgeKey left right)

@[simp] theorem localizedBondOrder_self (molecule : SemanticMolecule) (atom : ℕ) :
    molecule.localizedBondOrder atom atom = 0 := by
  simp [localizedBondOrder]

theorem localizedBondOrder_comm (molecule : SemanticMolecule) (left right : ℕ) :
    molecule.localizedBondOrder left right = molecule.localizedBondOrder right left := by
  by_cases same : left = right
  · subst right
    rfl
  · have reverse : right ≠ left := by exact fun equality => same equality.symm
    simp [localizedBondOrder, same, reverse, semanticEdgeKey_comm]

/-- On a graph-ready molecule, an extracted semantic record becomes exactly the corresponding
graph bond order. -/
theorem localizedBondOrder_eq_of_record
    (molecule : SemanticMolecule) (left right order : ℕ)
    (ready : molecule.LocalizedCIPGraphReady)
    (distinct : left ≠ right)
    (present : (semanticEdgeKey left right, order) ∈ molecule.localizedCovalentRecords) :
    molecule.localizedBondOrder left right = order := by
  unfold localizedBondOrder
  rw [if_neg distinct]
  exact localizedBondOrderAtKey_eq_of_mem_unique molecule.localizedCovalentRecords
    (semanticEdgeKey left right) order ready.2.2.2.2 present

/-- Absence of an unordered semantic bond record is reflected as graph order zero. -/
theorem localizedBondOrder_eq_zero_of_no_record
    (molecule : SemanticMolecule) (left right : ℕ)
    (absent : semanticEdgeKey left right ∉ molecule.localizedCovalentKeys) :
    molecule.localizedBondOrder left right = 0 := by
  by_cases same : left = right
  · simp [localizedBondOrder, same]
  · simp only [localizedBondOrder, if_neg same]
    exact localizedBondOrderAtKey_eq_zero_of_not_mem molecule.localizedCovalentRecords
      (semanticEdgeKey left right) absent

/-- Direct format-neutral constitutional graph.  No parser element conversion occurs here. -/
def toLocalizedMoleculeGraph (molecule : SemanticMolecule) :
    MoleculeGraph (Fin molecule.atomCount) where
  atomZ := fun atom => (molecule.atoms.get atom).element.atomicNumber
  atomMass := fun atom => (molecule.atoms.get atom).rule2MassPico?.getD 0
  formalCharge := fun atom => (molecule.atoms.get atom).formalCharge
  bond := fun left right => molecule.localizedBondOrder left.val right.val
  bond_symm := by
    intro left right
    exact molecule.localizedBondOrder_comm left.val right.val
  bond_self := by
    intro atom
    exact molecule.localizedBondOrder_self atom.val

@[simp] theorem toLocalizedMoleculeGraph_atomZ (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) :
    molecule.toLocalizedMoleculeGraph.atomZ atom =
      (molecule.atoms.get atom).element.atomicNumber := rfl

@[simp] theorem toLocalizedMoleculeGraph_atomMass (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) :
    molecule.toLocalizedMoleculeGraph.atomMass atom =
      (molecule.atoms.get atom).rule2MassPico?.getD 0 := rfl

/-- On every admitted input, the graph mass is exactly a source-backed Rule-2 datum.  Thus the
total graph constructor's internal `0` fallback cannot be observed through certified admission. -/
theorem toLocalizedMoleculeGraph_atomMass_eq_of_ready
    (molecule : SemanticMolecule) (ready : molecule.LocalizedCIPGraphReady)
    (atom : Fin molecule.atomCount) :
    ∃ mass,
      (molecule.atoms.get atom).rule2MassPico? = some mass ∧
        molecule.toLocalizedMoleculeGraph.atomMass atom = mass := by
  have membership : molecule.atoms.get atom ∈ molecule.atoms := List.get_mem _ _
  obtain ⟨mass, observed⟩ := ready.2.2.1 (molecule.atoms.get atom) membership
  refine ⟨mass, observed, ?_⟩
  change (molecule.atoms.get atom).rule2MassPico?.getD 0 = mass
  rw [observed]
  rfl

@[simp] theorem toLocalizedMoleculeGraph_formalCharge (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) :
    molecule.toLocalizedMoleculeGraph.formalCharge atom =
      (molecule.atoms.get atom).formalCharge := rfl

@[simp] theorem toLocalizedMoleculeGraph_bond (molecule : SemanticMolecule)
    (left right : Fin molecule.atomCount) :
    molecule.toLocalizedMoleculeGraph.bond left right =
      molecule.localizedBondOrder left.val right.val := rfl

/-- End-to-end constitutional edge refinement from an admitted semantic record to the graph. -/
theorem toLocalizedMoleculeGraph_bond_eq_of_record
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount) (order : ℕ)
    (ready : molecule.LocalizedCIPGraphReady)
    (distinct : left ≠ right)
    (present : (semanticEdgeKey left.val right.val, order) ∈
      molecule.localizedCovalentRecords) :
    molecule.toLocalizedMoleculeGraph.bond left right = order := by
  rw [toLocalizedMoleculeGraph_bond]
  apply molecule.localizedBondOrder_eq_of_record left.val right.val order ready
  · exact fun sameValue => distinct (Fin.ext sameValue)
  · exact present

/-- End-to-end nonedge reflection from the semantic record set to the graph. -/
theorem toLocalizedMoleculeGraph_bond_eq_zero_of_no_record
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount)
    (absent : semanticEdgeKey left.val right.val ∉ molecule.localizedCovalentKeys) :
    molecule.toLocalizedMoleculeGraph.bond left right = 0 := by
  rw [toLocalizedMoleculeGraph_bond]
  exact molecule.localizedBondOrder_eq_zero_of_no_record left.val right.val absent

/-- Exact adjacency reflection: on an admitted semantic molecule, a graph edge exists exactly when
the semantic record list contains a positive localized covalent order for that unordered pair. -/
theorem toLocalizedMoleculeGraph_adj_iff_record
    (molecule : SemanticMolecule) (ready : molecule.LocalizedCIPGraphReady)
    (left right : Fin molecule.atomCount) (distinct : left ≠ right) :
    molecule.toLocalizedMoleculeGraph.Adj left right ↔
      ∃ order,
        (semanticEdgeKey left.val right.val, order) ∈ molecule.localizedCovalentRecords ∧
          0 < order := by
  constructor
  · intro adjacent
    have keyPresent :
        semanticEdgeKey left.val right.val ∈ molecule.localizedCovalentKeys := by
      by_contra absent
      have zero := molecule.toLocalizedMoleculeGraph_bond_eq_zero_of_no_record left right absent
      exact (Nat.ne_of_gt adjacent) zero
    rw [localizedCovalentKeys, List.mem_map] at keyPresent
    obtain ⟨record, recordPresent, recordKey⟩ := keyPresent
    rcases record with ⟨key, order⟩
    simp only at recordKey
    subst key
    exact ⟨order, recordPresent,
      molecule.localizedCovalentRecord_order_positive
        (semanticEdgeKey left.val right.val) order recordPresent⟩
  · rintro ⟨order, present, positive⟩
    rw [MoleculeGraph.Adj,
      molecule.toLocalizedMoleculeGraph_bond_eq_of_record left right order ready distinct present]
    exact positive

/-- The graph bridge preserves the all-elements invariant at every vertex. -/
theorem toLocalizedMoleculeGraph_atomicNumber_supported (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) :
    0 < molecule.toLocalizedMoleculeGraph.atomZ atom ∧
      molecule.toLocalizedMoleculeGraph.atomZ atom ≤ 118 := by
  exact ⟨(molecule.atoms.get atom).element.positive,
    (molecule.atoms.get atom).element.atMost118⟩

end SemanticMolecule

/-- A structurally certified authority input whose constitution is already in the exact localized
closed-shell pair-bond domain of the current CIP graph. -/
structure CertifiedLocalizedCIPInput where
  certified : CertifiedAuthoritativeChemicalInput
  graphReady : certified.input.molecule.LocalizedCIPGraphReady

namespace CertifiedAuthoritativeChemicalInput

/-- Fail-closed admission to the direct all-element constitutional CIP graph. -/
def certifyLocalizedCIP? (certified : CertifiedAuthoritativeChemicalInput) :
    Option CertifiedLocalizedCIPInput :=
  if ready : certified.input.molecule.localizedCIPGraphReady? = true then
    some { certified := certified
           graphReady :=
             (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff
               certified.input.molecule).mp ready }
  else none

@[simp] theorem certifyLocalizedCIP?_isSome
    (certified : CertifiedAuthoritativeChemicalInput) :
    certified.certifyLocalizedCIP?.isSome = true ↔
      certified.input.molecule.LocalizedCIPGraphReady := by
  by_cases ready : certified.input.molecule.localizedCIPGraphReady? = true
  · have semanticReady :=
      (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff
        certified.input.molecule).mp ready
    simp [certifyLocalizedCIP?, ready, semanticReady]
  · have semanticNotReady :
        ¬ certified.input.molecule.LocalizedCIPGraphReady := by
      intro semanticReady
      exact ready ((SemanticMolecule.localizedCIPGraphReady?_eq_true_iff
        certified.input.molecule).mpr semanticReady)
    simp [certifyLocalizedCIP?, ready, semanticNotReady]

end CertifiedAuthoritativeChemicalInput

namespace CertifiedLocalizedCIPInput

/-- The exact graph supplied to constitutional CIP reasoning. -/
def moleculeGraph (input : CertifiedLocalizedCIPInput) :
    MoleculeGraph (Fin input.certified.input.molecule.atomCount) :=
  input.certified.input.molecule.toLocalizedMoleculeGraph

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
