import TetraStereo.OneCenter.LocalizedRawAdmissionCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Explicit raw-source transport into the localized CIP graph domain

`TetraStereo.OneCenter.LocalizedRawAdmission` proves the constructive converse of
`LocalizedReference.admitRawSpatial?_exact`, but it still starts from two supplied semantic facts:
a successful parser conversion `molecule.toSemanticMolecule? = some semantic` and a proof of the
existing graph-readiness predicate `semantic.LocalizedCIPGraphReady`.

This module removes both.  It derives the conversion from executable raw data (a frozen Rule-2 mass
datum for every parsed atom rules out the nonchemical `wildcard` sentinel) and proves all five
components of `SemanticMolecule.LocalizedCIPGraphReady` from transparent conditions on the parsed
atom and bond lists:

* `molecule.Admissible` (bounded, distinct bond endpoints and duplicate-free unordered endpoint
  keys);
* every parsed atom is non-aromatic (conversion then gives an explicit localized closed shell,
  because parser atoms always convert with zero unpaired electrons);
* every parsed atom has a frozen Rule-2 mass datum (`RawMolecule.Rule2MassesKnown`);
* every parsed bond spelling is one of `single`, `double`, `triple`, `up`, `down` (the localized
  covalent pair spellings; `unspecified` and `aromatic` are normalization inputs);
* the unordered endpoint keys of the parsed bonds are duplicate-free (the uniqueness component,
  transported through the exact record extraction below).

Charges, isotope labels, rings and multiple bonds are retained.  There is no acyclicity condition
and no bond-order-one restriction: `double` converts to order two and `triple` to order three, both
accepted by `SemanticInteraction.IsLocalizedCovalentPair`.

No admission or certification success is assumed.  The final theorems construct the executable
pipeline input from the raw conditions and a spatial list indexed by the parsed atoms.
-/

/-! ## The localized parser bond spellings -/

namespace ParsedBondKind

/-- Positive bond order of exactly the parser spellings whose semantic interaction is an explicitly
localized two-atom covalent pair.  `unspecified` and `aromatic` are normalization inputs and are
therefore excluded. -/
def localizedBondOrder? : ParsedBondKind → Option ℕ
  | .unspecified => none
  | .single => some 1
  | .double => some 2
  | .triple => some 3
  | .aromatic => none
  | .up => some 1
  | .down => some 1

/-- Propositional acceptance predicate: the spelling has a positive localized covalent order. -/
def IsLocalizedCovalent (kind : ParsedBondKind) : Prop :=
  ∃ order, kind.localizedBondOrder? = some order

@[simp] theorem localizedBondOrder?_isSome_iff (kind : ParsedBondKind) :
    kind.localizedBondOrder?.isSome = true ↔ kind.IsLocalizedCovalent :=
  Option.isSome_iff_exists

/-- The accepted raw spellings are exactly `single`, `double`, `triple`, `up`, and `down`. -/
theorem isLocalizedCovalent_iff (kind : ParsedBondKind) :
    kind.IsLocalizedCovalent ↔
      kind = .single ∨ kind = .double ∨ kind = .triple ∨ kind = .up ∨ kind = .down := by
  cases kind <;> simp [IsLocalizedCovalent, localizedBondOrder?]

/-- The only accepted spelling with localized order two is the ordinary double bond. -/
@[simp] theorem localizedBondOrder?_eq_some_two_iff (kind : ParsedBondKind) :
    kind.localizedBondOrder? = some 2 ↔ kind = .double := by
  cases kind <;> simp [localizedBondOrder?]

end ParsedBondKind

namespace SemanticInteraction

/-- Extracting the localized pair record from the semantic interaction of a raw bond is exactly the
raw unordered edge key together with the localized order of the parser spelling.  Unsupported
spellings contribute nothing. -/
theorem localizedCovalentRecord?_toSemanticInteraction (bond : RawBond) :
    bond.toSemanticInteraction.localizedCovalentRecord? =
      (bond.kind.localizedBondOrder?).map (fun order => (bond.edgeKey, order)) := by
  cases kindObserved : bond.kind <;>
    simp [kindObserved, ParsedBondKind.localizedBondOrder?, RawBond.toSemanticInteraction,
      SemanticInteraction.localizedCovalentRecord?, RawBond.edgeKey, semanticEdgeKey]

/-- Every supported raw bond converts to an explicitly localized positive-order covalent pair. -/
theorem isLocalizedCovalentPair_toSemanticInteraction (bond : RawBond)
    (supported : bond.kind.IsLocalizedCovalent) :
    bond.toSemanticInteraction.IsLocalizedCovalentPair := by
  rcases supported with ⟨order, orderEq⟩
  apply (SemanticInteraction.localizedCovalentRecord?_isSome bond.toSemanticInteraction).mp
  rw [localizedCovalentRecord?_toSemanticInteraction, orderEq]
  simp

end SemanticInteraction

namespace LocalizedRawGraphReadiness

/-! ## Transport of semantic atoms back to their parsed spelling -/

/-- Every atom of the converted semantic molecule is the checked conversion of a parsed atom at the
same list position.  This is the membership form of
`RawMolecule.toSemanticMolecule?_atomAt?`. -/
theorem exists_rawAtom_of_semantic_mem
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    {semanticAtom : SemanticAtom} (member : semanticAtom ∈ semantic.atoms) :
    ∃ rawAtom, rawAtom ∈ molecule.atoms ∧ rawAtom.toSemanticAtom? = some semanticAtom := by
  obtain ⟨index, indexedGet⟩ := List.mem_iff_get.mp member
  have semanticLookup : listGet? semantic.atoms index.val = some semanticAtom := by
    exact (listGet?_eq_some_get semantic.atoms index).trans (congrArg some indexedGet)
  have indexed := molecule.toSemanticMolecule?_atomAt? semantic converted index.val
  rw [semanticLookup] at indexed
  cases rawObserved : molecule.atomAt? index.val with
  | none => simp [rawObserved] at indexed
  | some rawAtom =>
      have rawConverted : rawAtom.toSemanticAtom? = some semanticAtom := by
        simpa [rawObserved] using indexed.symm
      have rawMember : rawAtom ∈ molecule.atoms :=
        listGet?_eq_some_implies_mem molecule.atoms index.val rawAtom
          (by simpa [RawMolecule.atomAt?] using rawObserved)
      exact ⟨rawAtom, rawMember, rawConverted⟩

/-- The raw and semantic Rule-2 mass lookups agree at every converted atom spelling.  The parsed
element cannot be the unknown wildcard, because conversion would have failed. -/
theorem rule2MassPico?_toSemanticAtom?
    (atom : AtomSpec) (semantic : SemanticAtom)
    (converted : atom.toSemanticAtom? = some semantic) :
    SemanticAtom.rule2MassPico? semantic =
      RawMolecule.rule2MassPico? atom.element atom.isotope? := by
  have exactFacts := AtomSpec.toSemanticAtom?_exact atom semantic converted
  have noWildcard : atom.element ≠ .wildcard := by
    intro unknown
    have present : atom.toSemanticAtom?.isSome = true := by simp [converted]
    exact (AtomSpec.toSemanticAtom?_isSome atom).mp present unknown
  simp [SemanticAtom.rule2MassPico?, RawMolecule.rule2MassPico?, noWildcard,
    exactFacts.1, exactFacts.2.1]

/-- A frozen Rule-2 mass datum for every parsed atom rules out the unknown wildcard sentinel, which
is exactly the totality condition of the checked parser conversion.  Consequently conversion
success does not have to be supplied separately by a caller. -/
theorem noWildcard_of_rule2MassesKnown
    (molecule : RawMolecule) (known : molecule.Rule2MassesKnown) :
    ∀ atom, atom ∈ molecule.atoms → atom.element ≠ .wildcard := by
  intro atom member unknown
  obtain ⟨mass, massEq⟩ := known atom member
  rw [unknown] at massEq
  simp [RawMolecule.rule2MassPico?] at massEq

/-! ## The five components of graph readiness -/

/-- Raw structural admission (`WellFormed`) is exactly the semantic structural condition through
the checked parser bridge. -/
theorem structurallyWellFormed_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (wellFormed : molecule.WellFormed) :
    semantic.StructurallyWellFormed :=
  (RawMolecule.toSemanticMolecule?_structurallyWellFormed_iff molecule semantic converted).mpr
    wellFormed

/-- Non-aromatic parsed atom spellings convert to explicitly localized closed-shell semantic atoms:
the conversion always sets `unpairedElectrons` to zero and preserves the aromatic-input flag. -/
theorem explicitLocalizedClosedShellAtoms_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (nonAromatic : ∀ atom, atom ∈ molecule.atoms → atom.aromatic = false) :
    semantic.ExplicitLocalizedClosedShellAtoms := by
  unfold SemanticMolecule.ExplicitLocalizedClosedShellAtoms
  intro semanticAtom member
  obtain ⟨rawAtom, rawMember, rawConverted⟩ :=
    exists_rawAtom_of_semantic_mem molecule semantic converted member
  have exactFacts := AtomSpec.toSemanticAtom?_exact rawAtom semanticAtom rawConverted
  unfold SemanticAtom.ExplicitLocalizedClosedShell
  exact ⟨exactFacts.2.2.2.1, by
    rw [exactFacts.2.2.2.2, nonAromatic rawAtom rawMember]⟩

/-- A frozen Rule-2 mass datum for every parsed atom transports to every converted semantic atom. -/
theorem allRule2MassesKnown_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (massesKnown : molecule.Rule2MassesKnown) :
    semantic.AllRule2MassesKnown := by
  unfold SemanticMolecule.AllRule2MassesKnown
  intro semanticAtom member
  obtain ⟨rawAtom, rawMember, rawConverted⟩ :=
    exists_rawAtom_of_semantic_mem molecule semantic converted member
  obtain ⟨mass, massEq⟩ := massesKnown rawAtom rawMember
  unfold SemanticAtom.Rule2MassKnown
  exact ⟨mass, by
    rw [rule2MassPico?_toSemanticAtom? rawAtom semanticAtom rawConverted, massEq]⟩

/-- Supported parsed bond spellings convert to explicitly localized positive-order covalent pairs.
This retains double and triple bonds. -/
theorem localizedCovalentPairsOnly_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (supported : ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent) :
    semantic.LocalizedCovalentPairsOnly := by
  unfold SemanticMolecule.LocalizedCovalentPairsOnly
  intro interaction member
  rw [RawMolecule.toSemanticMolecule?_interactions molecule semantic converted] at member
  obtain ⟨bond, bondMember, bondEq⟩ := List.mem_map.mp member
  rw [← bondEq]
  exact SemanticInteraction.isLocalizedCovalentPair_toSemanticInteraction bond
    (supported bond bondMember)

/-- On the supported domain, extracting the unordered keys of the localized records is exactly
mapping the raw edge key over the bond list. -/
private theorem localizedCovalentKeys_filterMap_eq
    (bonds : List RawBond)
    (supported : ∀ bond, bond ∈ bonds → bond.kind.IsLocalizedCovalent) :
    ((bonds.map RawBond.toSemanticInteraction).filterMap
        SemanticInteraction.localizedCovalentRecord?).map Prod.fst =
      bonds.map RawBond.edgeKey := by
  induction bonds with
  | nil => rfl
  | cons bond rest inductionHypothesis =>
      rcases supported bond (by simp) with ⟨order, orderEq⟩
      have recordCons :
          bond.toSemanticInteraction.localizedCovalentRecord? =
            some (bond.edgeKey, order) := by
        rw [SemanticInteraction.localizedCovalentRecord?_toSemanticInteraction, orderEq]
        rfl
      have tailSupported :
          ∀ item, item ∈ rest → item.kind.IsLocalizedCovalent :=
        fun item itemMember => supported item (by simp [itemMember])
      simp only [List.map_cons, List.filterMap_cons, recordCons]
      rw [inductionHypothesis tailSupported]

/-- Duplicate-free raw unordered endpoint keys transport to uniqueness of the extracted semantic
localized records. -/
theorem localizedCovalentKeys_eq_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (supported : ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent) :
    semantic.localizedCovalentKeys = molecule.bonds.map RawBond.edgeKey := by
  unfold SemanticMolecule.localizedCovalentKeys SemanticMolecule.localizedCovalentRecords
  rw [RawMolecule.toSemanticMolecule?_interactions molecule semantic converted]
  exact localizedCovalentKeys_filterMap_eq molecule.bonds supported

theorem localizedCovalentRecordsUnique_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (supported : ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent)
    (recordsUnique : molecule.BondRecordsUnique) :
    semantic.LocalizedCovalentRecordsUnique := by
  unfold SemanticMolecule.LocalizedCovalentRecordsUnique
  rw [localizedCovalentKeys_eq_raw molecule semantic converted supported]
  exact recordsUnique

/-! ## The explicit raw readiness gate -/

/-- Transparent raw-source conditions sufficient for the localized CIP graph domain.  There is no
wildcard condition: `Rule2MassesKnown` already excludes the unknown sentinel. -/
def RawLocalizedGraphSourceReady (molecule : RawMolecule) : Prop :=
  molecule.Admissible ∧
    (∀ atom, atom ∈ molecule.atoms → atom.aromatic = false) ∧
      molecule.Rule2MassesKnown ∧
        ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent

/-- Executable form of `RawLocalizedGraphSourceReady`, computed directly on the parsed atom and bond
lists. -/
def rawLocalizedGraphSourceReady? (molecule : RawMolecule) : Bool :=
  molecule.admissible? &&
    molecule.atoms.all (fun atom => decide (atom.aromatic = false)) &&
      molecule.rule2MassesKnown? &&
        molecule.bonds.all fun bond => bond.kind.localizedBondOrder?.isSome

/-- Kernel-checked reflection of the executable raw readiness gate. -/
@[simp] theorem rawLocalizedGraphSourceReady?_eq_true_iff (molecule : RawMolecule) :
    rawLocalizedGraphSourceReady? molecule = true ↔
      RawLocalizedGraphSourceReady molecule := by
  simp [rawLocalizedGraphSourceReady?, RawLocalizedGraphSourceReady, RawMolecule.Admissible,
    ParsedBondKind.IsLocalizedCovalent, and_assoc]

/-- All five graph-readiness components are derived from the raw gate and the checked conversion. -/
theorem localizedCIPGraphReady_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (rawReady : RawLocalizedGraphSourceReady molecule) :
    semantic.LocalizedCIPGraphReady := by
  unfold RawLocalizedGraphSourceReady at rawReady
  have wellFormed : molecule.WellFormed := rawReady.1.1
  have recordsUnique : molecule.BondRecordsUnique := rawReady.1.2
  have nonAromatic : ∀ atom, atom ∈ molecule.atoms → atom.aromatic = false := rawReady.2.1
  have massesKnown : molecule.Rule2MassesKnown := rawReady.2.2.1
  have supported : ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent := rawReady.2.2.2
  unfold SemanticMolecule.LocalizedCIPGraphReady
  exact
    ⟨structurallyWellFormed_of_raw molecule semantic converted wellFormed,
      explicitLocalizedClosedShellAtoms_of_raw molecule semantic converted nonAromatic,
      allRule2MassesKnown_of_raw molecule semantic converted massesKnown,
      localizedCovalentPairsOnly_of_raw molecule semantic converted supported,
      localizedCovalentRecordsUnique_of_raw molecule semantic converted supported recordsUnique⟩

/-- The raw gate alone (without a supplied conversion identity) yields a semantic molecule in the
localized CIP graph domain.  Conversion totality is derived from `Rule2MassesKnown`; it is not an
additional assumption. -/
theorem exists_localizedCIPGraphReady_of_raw
    (molecule : RawMolecule) (rawReady : RawLocalizedGraphSourceReady molecule) :
    ∃ semantic : SemanticMolecule,
      molecule.toSemanticMolecule? = some semantic ∧
        semantic.LocalizedCIPGraphReady := by
  unfold RawLocalizedGraphSourceReady at rawReady
  have massesKnown : molecule.Rule2MassesKnown := rawReady.2.2.1
  have noWildcard := noWildcard_of_rule2MassesKnown molecule massesKnown
  have someTrue : molecule.toSemanticMolecule?.isSome = true :=
    (RawMolecule.toSemanticMolecule?_isSome molecule).mpr noWildcard
  obtain ⟨semantic, converted⟩ := Option.isSome_iff_exists.mp someTrue
  exact ⟨semantic, converted,
    localizedCIPGraphReady_of_raw molecule semantic converted rawReady⟩

/-! ## Raw admission into the localized reference pipeline -/

/-- **Raw admission from source data alone.**  Given only the explicit raw gate and one coordinate
per parsed atom, the actual executable `LocalizedReference.admitRawSpatial?` returns some input.
The input preserves the conversion image of the parsed molecule, agrees with the parsed structure,
and carries exactly the supplied spatial configuration.

Both previously explicit semantic assumptions — conversion success and
`semantic.LocalizedCIPGraphReady` — are derived here.  No admission, certification, or acceptance
success is assumed. -/
theorem admitRawSpatial?_of_raw
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial := by
  unfold RawLocalizedGraphSourceReady at rawReady
  have massesKnown : molecule.Rule2MassesKnown := rawReady.2.2.1
  have noWildcard := noWildcard_of_rule2MassesKnown molecule massesKnown
  have someTrue : molecule.toSemanticMolecule?.isSome = true :=
    (RawMolecule.toSemanticMolecule?_isSome molecule).mpr noWildcard
  obtain ⟨semantic, converted⟩ := Option.isSome_iff_exists.mp someTrue
  have ready : semantic.LocalizedCIPGraphReady :=
    localizedCIPGraphReady_of_raw molecule semantic converted rawReady
  obtain ⟨input, rawEq, moleculeEq, agreement, spatialEq⟩ :=
    LocalizedRawAdmission.admitRawSpatial?_complete_of_rawCount molecule semantic spatial
      converted ready spatialLength
  exact ⟨semantic, input, converted, rawEq, moleculeEq, agreement, spatialEq⟩

/-- Variant for a caller that already fixed the semantic conversion identity. -/
theorem admitRawSpatial?_of_raw_converted
    (molecule : RawMolecule) (semantic : SemanticMolecule) (spatial : SpatialConfiguration)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ input : LocalizedReference.Input,
      LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
        input.certified.certified.input.molecule = semantic ∧
          molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
            input.certified.certified.input.spatial? = some spatial :=
  LocalizedRawAdmission.admitRawSpatial?_complete_of_rawCount molecule semantic spatial converted
    (localizedCIPGraphReady_of_raw molecule semantic converted rawReady) spatialLength

/-- Executable-call-site form: admission succeeds whenever the computed raw readiness check passes
and one coordinate per parsed atom is supplied. -/
theorem admitRawSpatial?_of_rawCheck
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (checked : rawLocalizedGraphSourceReady? molecule = true)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial :=
  admitRawSpatial?_of_raw molecule spatial
    ((rawLocalizedGraphSourceReady?_eq_true_iff molecule).mp checked) spatialLength

/-! ## The no-double source-record pipeline -/

/-- Raw spelling condition corresponding exactly to the semantic no-order-two restriction on the
supported domain: no parsed bond has the ordinary `double` spelling. -/
def NoDoubleBondKinds (molecule : RawMolecule) : Prop :=
  ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .double

def noDoubleBondKinds? (molecule : RawMolecule) : Bool :=
  molecule.bonds.all fun bond => decide (bond.kind ≠ .double)

@[simp] theorem noDoubleBondKinds?_eq_true_iff (molecule : RawMolecule) :
    noDoubleBondKinds? molecule = true ↔ NoDoubleBondKinds molecule := by
  simp [noDoubleBondKinds?, NoDoubleBondKinds]

private theorem filterMap_localizedCovalentRecords_no_two
    (bonds : List RawBond)
    (supported : ∀ bond, bond ∈ bonds → bond.kind.IsLocalizedCovalent)
    (noDouble : ∀ bond, bond ∈ bonds → bond.kind ≠ .double) :
    ∀ record, record ∈ (bonds.map RawBond.toSemanticInteraction).filterMap
        SemanticInteraction.localizedCovalentRecord? → record.2 ≠ 2 := by
  induction bonds with
  | nil => simp
  | cons bond rest inductionHypothesis =>
      rcases supported bond (by simp) with ⟨order, orderEq⟩
      have orderNeTwo : order ≠ 2 := by
        intro orderTwo
        rw [orderTwo] at orderEq
        exact noDouble bond (by simp)
          ((ParsedBondKind.localizedBondOrder?_eq_some_two_iff bond.kind).mp orderEq)
      have recordCons :
          bond.toSemanticInteraction.localizedCovalentRecord? =
            some (bond.edgeKey, order) := by
        rw [SemanticInteraction.localizedCovalentRecord?_toSemanticInteraction, orderEq]
        rfl
      intro record member
      simp only [List.map_cons, List.filterMap_cons, recordCons] at member
      rcases List.mem_cons.mp member with recordEq | tailMember
      · subst record
        exact orderNeTwo
      · exact inductionHypothesis
          (fun item itemMember => supported item (by simp [itemMember]))
          (fun item itemMember => noDouble item (by simp [itemMember]))
          record tailMember

/-- On the supported domain, the raw no-double spelling condition is exactly the semantic
source-record restriction. -/
theorem noLocalizedDoubleBondRecords_of_raw
    (molecule : RawMolecule) (semantic : SemanticMolecule)
    (converted : molecule.toSemanticMolecule? = some semantic)
    (supported : ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent)
    (noDoubleKinds : NoDoubleBondKinds molecule) :
    semantic.NoLocalizedDoubleBondRecords := by
  unfold SemanticMolecule.NoLocalizedDoubleBondRecords
  unfold SemanticMolecule.localizedCovalentRecords
  rw [RawMolecule.toSemanticMolecule?_interactions molecule semantic converted]
  exact filterMap_localizedCovalentRecords_no_two molecule.bonds supported noDoubleKinds

/-- **Raw admission into the no-double pipeline.**  The raw gate plus the raw spelling condition
"no parsed double bond" constructs the actual `LocalizedNoDoubleReference.Input`.  Triple bonds
remain permitted, so this is not a bond-order-one restriction. -/
theorem admitRawSpatial?_of_raw_noDouble
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (noDoubleKinds : NoDoubleBondKinds molecule)
    (spatialLength : spatial.positions.length = molecule.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedNoDoubleReference.Input),
      molecule.toSemanticMolecule? = some semantic ∧
        LocalizedNoDoubleReference.admitRawSpatial? molecule spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.AuthoritativeStructureAgreement input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                input.NoDoubleRecords := by
  unfold RawLocalizedGraphSourceReady at rawReady
  have massesKnown : molecule.Rule2MassesKnown := rawReady.2.2.1
  have noWildcard := noWildcard_of_rule2MassesKnown molecule massesKnown
  have someTrue : molecule.toSemanticMolecule?.isSome = true :=
    (RawMolecule.toSemanticMolecule?_isSome molecule).mpr noWildcard
  obtain ⟨semantic, converted⟩ := Option.isSome_iff_exists.mp someTrue
  have ready : semantic.LocalizedCIPGraphReady :=
    localizedCIPGraphReady_of_raw molecule semantic converted rawReady
  have supported : ∀ bond, bond ∈ molecule.bonds → bond.kind.IsLocalizedCovalent := rawReady.2.2.2
  have noDouble : semantic.NoLocalizedDoubleBondRecords :=
    noLocalizedDoubleBondRecords_of_raw molecule semantic converted supported noDoubleKinds
  have semanticCount : semantic.atomCount = molecule.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount molecule semantic converted
  have spatialLength' : spatial.positions.length = semantic.atomCount := by
    rw [semanticCount]
    exact spatialLength
  obtain ⟨input, rawEq, moleculeEq, agreement, spatialEq, inputNoDouble⟩ :=
    LocalizedRawAdmission.admitRawSpatial?_complete_noDouble molecule semantic spatial converted
      ready noDouble spatialLength'
  exact ⟨semantic, input, converted, rawEq, moleculeEq, agreement, spatialEq, inputNoDouble⟩

end LocalizedRawGraphReadiness

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.ParsedBondKind.localizedBondOrder?_isSome_iff
assert_kernel_only TetraStereo.OneCenter.ParsedBondKind.isLocalizedCovalent_iff
assert_kernel_only TetraStereo.OneCenter.ParsedBondKind.localizedBondOrder?_eq_some_two_iff
assert_kernel_only
  TetraStereo.OneCenter.SemanticInteraction.localizedCovalentRecord?_toSemanticInteraction
assert_kernel_only
  TetraStereo.OneCenter.SemanticInteraction.isLocalizedCovalentPair_toSemanticInteraction
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.exists_rawAtom_of_semantic_mem
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.rule2MassPico?_toSemanticAtom?
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.noWildcard_of_rule2MassesKnown
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.structurallyWellFormed_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.explicitLocalizedClosedShellAtoms_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.allRule2MassesKnown_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.localizedCovalentPairsOnly_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.localizedCovalentKeys_eq_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.localizedCovalentRecordsUnique_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.rawLocalizedGraphSourceReady?_eq_true_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.localizedCIPGraphReady_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.exists_localizedCIPGraphReady_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.admitRawSpatial?_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.admitRawSpatial?_of_raw_converted
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.admitRawSpatial?_of_rawCheck
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.noDoubleBondKinds?_eq_true_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.noLocalizedDoubleBondRecords_of_raw
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRawGraphReadiness.admitRawSpatial?_of_raw_noDouble
