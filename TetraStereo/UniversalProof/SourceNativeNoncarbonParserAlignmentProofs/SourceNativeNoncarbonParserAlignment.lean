import TetraStereo.KernelOnly
import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization
import TetraStereo.OneCenter.CIPP93TrigonalPyramidalIntegration
import TetraStereo.OneCenter.IUPACP93NoncarbonTetrahedralAuthorityCarrier
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeNoncarbonParserAlignmentProofs.SourceNativeNoncarbonParserAlignment

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.Rule6HandednessSemantics
open TetraStereo.OneCenter.BlueBookP93.TrigonalPyramidal
open TetraStereo.OneCenter.BlueBookP93.NoncarbonTetrahedra.Production
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence





















































/-! ## 1. The supported named-family and Group 14 subset -/

/-- Supported named-family and Group 14 noncarbon central-element atomic numbers: boron, nitrogen, phosphorus, arsenic,
antimony, bismuth, sulfur, selenium, tellurium (the carrier's named families) together with the
P-93.2.6 Group 14 centres silicon, germanium, tin and lead. Carbon (6) is excluded.
This implementation subset is not exhaustive P-93.2 applicability. -/
def NoncarbonCentralAtomicNumber (atomicNumber : Nat) : Prop :=
  atomicNumber ∈ ([5, 7, 14, 15, 16, 32, 33, 34, 50, 51, 52, 82, 83] : List Nat)

instance (atomicNumber : Nat) : Decidable (NoncarbonCentralAtomicNumber atomicNumber) := by
  unfold NoncarbonCentralAtomicNumber
  infer_instance

theorem noncarbonCentralAtomicNumber_carbon_false : ¬ NoncarbonCentralAtomicNumber 6 := by
  decide

theorem noncarbonCentralAtomicNumber_silicon_true : NoncarbonCentralAtomicNumber 14 := by
  decide

/-- Atom-specific noncarbon comparator over a semantic source center.  It reads the actual central
element; it is not a whole-molecule element whitelist. -/
def NoncarbonSemanticCenter (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) : Prop :=
  NoncarbonCentralAtomicNumber (source.molecule.atoms.get center).element.atomicNumber

instance (source : AuthoritativeChemicalInput) (center : source.AromaticCanonicalAtom) :
    Decidable (NoncarbonSemanticCenter source center) := by
  unfold NoncarbonSemanticCenter
  infer_instance

/-! ## 2. Actual P-93.2 normalization preserves the central frame -/

/-- The actual P-93.2 effective-graph quotient preserves, at every real raw index carrying a written
parity, the central element, isotope, written parity and the full written-neighbour frame.  It goes
through the file's actual `normalizeAtom`/`normalize` definitions, not a re-implementation. -/
theorem normalize_preserves_center_frame (mol : RawMolecule) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity)
    (observed : mol.atomAt? index = some spec)
    (parityObserved : spec.tetrahedral? = some parity) :
    ∃ normalized, (normalize mol).atomAt? index = some normalized ∧
      normalized.element = spec.element ∧ normalized.isotope? = spec.isotope? ∧
        normalized.tetrahedral? = some parity ∧
          (normalize mol).writtenNeighbors index = mol.writtenNeighbors index := by
  refine ⟨normalizeAtom mol index spec, ?_, ?_, ?_, ?_, ?_⟩
  · simp [normalize_atomAt?, observed]
  · exact normalizeAtom_element mol index spec
  · exact normalizeAtom_isotope mol index spec
  · simp [normalizeAtom_tetrahedral, parityObserved]
  · exact normalize_writtenNeighbors mol index

/-- The central atomic number is preserved by the P-93.2 quotient: a noncarbon center stays
noncarbon. -/
theorem normalize_preserves_center_atomicNumber (mol : RawMolecule) (index : Nat) (spec : AtomSpec)
    (observed : mol.atomAt? index = some spec) :
    (normalize mol).atomAt? index = some (normalizeAtom mol index spec) ∧
      (normalizeAtom mol index spec).element.atomicNumber = spec.element.atomicNumber :=
  ⟨by simp [normalize_atomAt?, observed],
    congrArg Element.atomicNumber (normalizeAtom_element mol index spec)⟩

/-- The P-93.2 quotient does not move the actual raw written-neighbour frame, so a downstream parser
channel reads the same written order on `normalize mol`. -/
theorem rawWrittenLigandFrame_normalize (mol : RawMolecule)
    (center : Fin (normalize mol).atomCount) :
    rawWrittenLigandFrame (normalize mol) center = mol.writtenNeighbors center.val := by
  simp [rawWrittenLigandFrame]

/-! ## 3. Source-bound noncarbon written-order alignment -/

/-- Source-bound noncarbon parser written-order alignment at one recovered occurrence center.  It
records the actual recovered semantic center, its genuine P-93.2 noncarbon identity, the actual raw
written-exact certificate, the actual declarative reroot frame and the actual raw-written/endpoint
`ExactSlotAlignment`.  No expected label, key, sort or success is stored. -/
structure NoncarbonParserWrittenAlignment (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) (slots : List Nat) : Prop where
  /-- The recovered semantic center of the occurrence target. -/
  recovered : source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center
  /-- The recovered center is genuinely noncarbon under the P-93.2 domain. -/
  noncarbon : NoncarbonSemanticCenter source center.1
  /-- The actual raw written-neighbour exactness certificate is retained. -/
  writtenNeighborExact : molecule.WrittenNeighborExact
  /-- The actual declarative reroot frame judgment of the returned cursors. -/
  children : source.DeclarativeAromaticCanonicalRerootChildren
    { occurrence := target, previous? := none } roots
  /-- The actual raw-written/endpoint-ID correspondence through the conversion-only parser index. -/
  matching : ExactSlotAlignment
    (rawWrittenLigandFrame molecule
      (parserIndexViaConversion molecule source agreement center))
    (occurrenceRootIDs source roots) slots

/-- Fail-closed noncarbon alignment matcher: recover the actual center, refuse immediately unless it
is genuinely noncarbon, recover the actual returned frame, and run the finite endpoint-ID matcher.
No caller permutation, label or success is an input. -/
noncomputable def noncarbonParserSlotAlignment? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.toSemanticMolecule? = some source.molecule) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) : Option (List Nat) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  if NoncarbonSemanticCenter source center.1 then
    let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
    findSlotAlignment?
      (rawWrittenLigandFrame molecule
        (parserIndexViaConversion molecule source agreement center))
      (occurrenceRootIDs source roots)
  else
    none

/-- Every successful noncarbon alignment has the complete source-bound meaning: actual recovered
center, genuine noncarbon identity, actual written-exact certificate, actual declarative reroot
frame and actual endpoint-ID correspondence. -/
theorem noncarbonParserSlotAlignment?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) (slots : List Nat)
    (computed : noncarbonParserSlotAlignment? molecule source agreement target = some slots) :
    ∃ center roots,
      NoncarbonParserWrittenAlignment molecule source agreement writtenExact target center roots
        slots := by
  unfold noncarbonParserSlotAlignment? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      by_cases eligible : NoncarbonSemanticCenter source center.1
      · simp [centerComputed, eligible] at computed
        cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
        | none => simp [rootsComputed] at computed
        | some roots =>
            cases found : findSlotAlignment?
                (rawWrittenLigandFrame molecule
                  (parserIndexViaConversion molecule source agreement center))
                (occurrenceRootIDs source roots) with
            | none => simp [rootsComputed, found] at computed
            | some positions =>
                simp [rootsComputed, found] at computed
                subst slots
                exact ⟨center, roots, centerComputed, eligible, writtenExact,
                  source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots rootsComputed,
                  findSlotAlignment?_sound _ _ positions found⟩
      · simp [centerComputed, eligible] at computed

/-- Exact reverse transport of the conversion-only parser index used by the alignment: the recovered
raw index maps back to the actual semantic center index. -/
theorem noncarbonParserWrittenAlignment_index_converted (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    molecule.convertedAtomIndex source agreement
        (parserIndexViaConversion molecule source agreement center) = center.val :=
  parserIndexViaConversion_converted molecule source agreement center

/-- The `i`-th returned occurrence endpoint ID is literally the raw written neighbour at the `i`-th
aligned slot: the alignment pins the actual raw written order against the actual returned frame. -/
theorem noncarbonParserWrittenAlignment_rawWritten_eq_rootID (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) (slots : List Nat)
    (alignment : NoncarbonParserWrittenAlignment molecule source agreement writtenExact target
      center roots slots) (index : Fin 4) :
    slots[index.val]?.map
        (fun slot =>
          (rawWrittenLigandFrame molecule
            (parserIndexViaConversion molecule source agreement center))[slot]?) =
      (occurrenceRootIDs source roots)[index.val]? := by
  have mapped := congrArg
    (fun values : List (Option Nat) => values[index.val]?) alignment.matching.2.2.2
  simpa only [List.getElem?_map] using mapped

/-! ## 4. Independently meaningful returned label -/




def NoncarbonParserDescriptorMeaning (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target view ruleFuel
      descriptor ∧
    ∃ center, source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
      NoncarbonSemanticCenter source center.1



noncomputable def noncarbonParserDescriptor? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  if NoncarbonSemanticCenter source center.1 then
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel
  else
    none

/-- Every emitted noncarbon descriptor has the complete meaning above. -/
theorem noncarbonParserDescriptor?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : noncarbonParserDescriptor? molecule source agreement writtenExact target view ruleFuel =
      some descriptor) :
    NoncarbonParserDescriptorMeaning molecule source agreement writtenExact target view ruleFuel
      descriptor := by
  unfold noncarbonParserDescriptor? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      by_cases eligible : NoncarbonSemanticCenter source center.1
      · simp [centerComputed, eligible] at computed
        exact ⟨constitutionParserRichDescriptor?_sound molecule source agreement writtenExact
          target view ruleFuel descriptor computed, center, centerComputed, eligible⟩
      · simp [centerComputed, eligible] at computed

/-! ## 5. Whole-pipeline P-93.2 frame preservation

The production entry point `normalizeRawMoleculeP93` now freezes every atom's exact *source* hydrogen
count (`RawMolecule.freezeSourceHydrogenCounts`) **before** the P-93.2 quotient, and its parsed
projection then applies default-bond normalization to the frozen molecule:

  `(normalizeRawMoleculeP93 mol cycles).parsed
     = (normalize (freezeSourceHydrogenCounts mol)).normalizeUnspecifiedBonds`.

Consequently the parsed atom at a real source index is the quotient of the *frozen* source atom, not
of the literal source atom: for an unbracketed organic-subset atom the hydrogen policy is the
derived `some (mol.hydrogenCountAt index)` rather than `none`.  `p93Parsed_atomAt?_eq` is the exact
projection.  Freezing is a pure copy of the source count computed by the shared
`RawSourceHydrogenPolicy` API; no hydrogen equality is assumed anywhere below.  Element, isotope,
input parity and the written-neighbour frame are preserved by both steps, so the centre-frame
conclusions are unchanged. -/

@[simp] theorem normalizeUnspecifiedBonds_atomAt? (mol : RawMolecule) (index : Nat) :
    mol.normalizeUnspecifiedBonds.atomAt? index = mol.atomAt? index := rfl

/-- Exact parsed atom projection of the hydrogen-frozen P-93.2 entry point.  At a real source index
the parsed atom is the quotient (at that index) of the source specification whose hydrogen policy
has been replaced by the exact source count `mol.hydrogenCountAt index`.  The count is *computed* by
`RawMolecule.freezeSourceHydrogenCounts` from the source graph; it is not an extra hypothesis. -/
theorem p93Parsed_atomAt?_eq (mol : RawMolecule) (cycles : List AromaticCycle)
    (index : Nat) (spec : AtomSpec) (observed : mol.atomAt? index = some spec) :
    (normalizeRawMoleculeP93 mol cycles).parsed.atomAt? index =
      some (normalizeAtom (RawMolecule.freezeSourceHydrogenCounts mol) index
        { spec with explicitHydrogens? := some (mol.hydrogenCountAt index) }) := by
  rw [normalizeRawMoleculeP93_parsed mol cycles, normalizeUnspecifiedBonds_atomAt?, normalize_atomAt?,
    RawMolecule.freezeSourceHydrogenCounts_atomAt?_spec mol index spec observed]
  rfl

/-- The actual parsed molecule of the P-93.2 entry point `normalizeRawMoleculeP93` preserves the same
central element/isotope/parity/written frame.  The proof reads the exact frozen-source atom
projection and then applies the quotient invariants; the theorem statement is unchanged from the
pre-freezing API. -/
theorem p93Parsed_preserves_center_frame (mol : RawMolecule) (cycles : List AromaticCycle)
    (index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (observed : mol.atomAt? index = some spec)
    (parityObserved : spec.tetrahedral? = some parity) :
    ∃ normalized, (normalizeRawMoleculeP93 mol cycles).parsed.atomAt? index = some normalized ∧
      normalized.element = spec.element ∧ normalized.isotope? = spec.isotope? ∧
        normalized.tetrahedral? = some parity ∧
          (normalizeRawMoleculeP93 mol cycles).parsed.writtenNeighbors index =
            mol.writtenNeighbors index := by
  refine ⟨normalizeAtom (RawMolecule.freezeSourceHydrogenCounts mol) index
    { spec with explicitHydrogens? := some (mol.hydrogenCountAt index) }, ?_, ?_, ?_, ?_, ?_⟩
  · exact p93Parsed_atomAt?_eq mol cycles index spec observed
  · simp
  · simp
  · simp [parityObserved]
  · rw [normalizeRawMoleculeP93_parsed mol cycles,
      RawMolecule.normalizeUnspecifiedBonds_writtenNeighbors, normalize_writtenNeighbors,
      RawMolecule.freezeSourceHydrogenCounts_writtenNeighbors]

/-! ## 6. Four-real frame and the three-real-plus-lone-pair refusal -/

/-- The four *real* written-ligand frame: four distinct materialized written neighbours.  This is the
frame the noncarbon parser alignment consumes. -/
def FourRealWrittenLigandFrame (mol : RawMolecule) (center : Nat) : Prop :=
  (mol.writtenNeighbors center).Nodup ∧
    (∀ ligand ∈ mol.writtenNeighbors center, ligand < mol.atomCount) ∧
      (mol.writtenNeighbors center).length = 4

/-- A committed written three-coordinate `@`/`@@` phantom frame is never a four-real frame.  Its
fourth position is the notional phantom, not a physical atom. -/
theorem lonePairFrame_not_fourReal (mol : RawMolecule) (center : Nat)
    (frame : WrittenConfigurationFrame mol center) :
    ¬ FourRealWrittenLigandFrame mol center := by
  intro four
  have three := frame.three_physical
  have fourLength := four.2.2
  omega

/-- Silicon is not in the P-93.3 phantom element family. -/
theorem elementSupportsPhantom_silicon_false : ¬ ElementSupportsPhantom Element.Si := by
  decide

/-- No written three-coordinate phantom frame exists at a silicon center: the element gate is the
exact P-93.3 main-group family and excludes silicon. -/
theorem silicon_writtenConfigurationFrame_unsupported (mol : RawMolecule) (center : Nat)
    (spec : AtomSpec) (observed : mol.atomAt? center = some spec) (silicon : spec.element = Element.Si) :
    ¬ Nonempty (WrittenConfigurationFrame mol center) := by
  rintro ⟨frame⟩
  have atomEq : frame.atom = spec := by
    have : some frame.atom = some spec := by rw [← frame.atom_eq, observed]
    exact Option.some.inj this
  have supported : ElementSupportsPhantom frame.atom.element := frame.element_supported
  rw [atomEq, silicon] at supported
  exact elementSupportsPhantom_silicon_false supported

/-- The exact refusal boundary for a three-real-coordinate noncarbon silicon center: it is neither a
four-real frame nor a supported written phantom frame.  A four-real silicon center is unaffected;
this is the "three-real plus lone pair" refusal and it is not a general lone-pair claim. -/
theorem silicon_threeCoordinate_refused (mol : RawMolecule) (center : Nat) (spec : AtomSpec)
    (observed : mol.atomAt? center = some spec) (silicon : spec.element = Element.Si)
    (three : (mol.writtenNeighbors center).length = 3) :
    (¬ FourRealWrittenLigandFrame mol center) ∧ ¬ Nonempty (WrittenConfigurationFrame mol center) :=
  ⟨fun four => by have := four.2.2; omega,
    silicon_writtenConfigurationFrame_unsupported mol center spec observed silicon⟩

/-- Production materializes exactly the independently specified notional phantom frame. -/
theorem phantom_production_eq (mol : RawMolecule) (center : Nat)
    (frame : WrittenConfigurationFrame mol center) :
    mol.ligandsWithLonePair center = writtenPhantomFrame mol center :=
  ligandsWithLonePair_eq_writtenPhantomFrame mol center frame

/-- Genuine virtual provenance shape certificate for a written phantom frame. -/
theorem phantom_frame_certificate (mol : RawMolecule) (center : Nat)
    (frame : WrittenConfigurationFrame mol center) (exact : mol.WrittenNeighborExact) :
    NotionalTetrahedralFrameCertificate mol center :=
  writtenConfigurationFrame_certificate mol center frame exact

/-- The phantom sentinel `mol.atomCount` is genuinely virtual: it is always present in the notional
frame and never names a materialized physical atom.  The extension therefore never invents a
physical atom index. -/
theorem phantom_sentinel_not_materialized (mol : RawMolecule) (center : Nat)
    (_frame : WrittenConfigurationFrame mol center) :
    mol.atomCount ∈ writtenPhantomFrame mol center ∧
      ¬ (∃ atom, mol.atomAt? mol.atomCount = some atom) := by
  refine ⟨atomCount_mem_writtenPhantomFrame mol center, ?_⟩
  rintro ⟨atom, observed⟩
  have bound := listGet?_eq_some_implies_lt mol.atoms mol.atomCount atom
    (by simpa [RawMolecule.atomAt?] using observed)
  simp [RawMolecule.atomCount] at bound

/-! ## 7. Genuine P-93.2 Group 14 authority correspondence -/

/-- The P-93.2.6 Group 14 silicon family names atomic number 14. -/
theorem group14_atomicNumber_silicon : P93NoncarbonGroup14AtomicNumber .silicon = 14 := rfl

/-- No P-93.2.6 Group 14 family names carbon. -/
theorem group14_atomicNumber_ne_carbon
    (family : BlueBookP93.NoncarbonTetrahedra.NoncarbonGroup14Center) :
    P93NoncarbonGroup14AtomicNumber family ≠ 6 := by
  cases family <;> decide

/-- The P-93.2.6 silicon atomic number lies in the supported noncarbon subset. -/
theorem silicon_is_p93_noncarbon :
    NoncarbonCentralAtomicNumber (P93NoncarbonGroup14AtomicNumber .silicon) := by
  decide

/-! ## 8. Closed genuinely noncarbon silicon source with four real distinct ligands

The literal `SiFClBrI` constitution carries a real silicon center, four distinct real halogens, a
copied `@@` (`clockwise`) annotation and a pinned parser diagram. The facts below derive the actual
conversion, record agreement, the genuine noncarbon center, the actual written frame and the
alignment existence and rich R emission with independent meaning. No expected label, keys, sort
or source approval is assumed. -/

namespace ClosedSiliconTetrahedral

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness

def siliconAtom : SemanticAtom := { element := ⟨14, by decide, by decide⟩ }
def fluorineAtom : SemanticAtom := { element := ⟨9, by decide, by decide⟩ }
def chlorineAtom : SemanticAtom := { element := ⟨17, by decide, by decide⟩ }
def bromineAtom : SemanticAtom := { element := ⟨35, by decide, by decide⟩ }
def iodineAtom : SemanticAtom := { element := ⟨53, by decide, by decide⟩ }

/-- The literal silicon tetrahalide semantic molecule: center `0`, distinct ligands `F`, `Cl`, `Br`,
`I` at indices `1`, `2`, `3`, `4`. -/
def molecule : SemanticMolecule :=
  { atoms := [siliconAtom, fluorineAtom, chlorineAtom, bromineAtom, iodineAtom]
    interactions :=
      [⟨[0, 1], .covalent 1⟩, ⟨[0, 2], .covalent 1⟩,
       ⟨[0, 3], .covalent 1⟩, ⟨[0, 4], .covalent 1⟩] }

/-- The literal parser constitution with the copied silicon `@@` (`clockwise`) annotation. -/
def raw : RawMolecule where
  atoms := [{ AtomSpec.aliphatic .Si with tetrahedral? := some TetrahedralInputParity.clockwise },
    AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I]
  bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]

/-- The parser-only noncarbon source: the exact conversion semantic molecule plus the literal
raw-parser diagram.  No spatial channel is introduced. -/
def source : AuthoritativeChemicalInput :=
  { molecule := molecule, diagram? := some raw.toDiagramConfiguration }

/-- Successful conversion lands exactly on the silicon semantic molecule. -/
theorem raw_toSemanticMolecule : raw.toSemanticMolecule? = some molecule := by
  decide +kernel

/-- The actual raw record carries the `WrittenNeighborExact` certificate. -/
theorem raw_writtenExact : raw.WrittenNeighborExact :=
  (raw.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

/-- The true raw written order at the silicon is the actual bond-list order. -/
theorem raw_written_endpoints : raw.writtenNeighbors 0 = [1, 2, 3, 4] := by
  decide +kernel

/-- The silicon source satisfies conversion-pinned actual record agreement. -/
theorem source_annotationAgreement : RawAnnotationAgreement raw source :=
  ⟨raw_toSemanticMolecule,
    (rawAnnotationAgreementIssues_eq_nil_iff raw source).mp (by decide +kernel)⟩

local instance : NeZero source.molecule.atomCount := ⟨by change (5 : Nat) ≠ 0; decide⟩

/-- The silicon centre's canonical neighbour finset is exactly the four real halogens. -/
theorem center_neighbors : source.aromaticCanonicalNeighborFinset 0 = {1, 2, 3, 4} := by
  ext atom
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  unfold AromaticCanonicalAdjacent
  decide +revert +kernel

/-- The actual perceived tetrahedral center of the silicon source. -/
noncomputable def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨0, (source.mem_aromaticCanonicalTetrahedralCenterSet_iff 0).mpr ⟨by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel, by rw [center_neighbors]; decide +kernel⟩⟩

theorem center_val : (center : source.AromaticCanonicalAtom).val = 0 := rfl

/-- The actual central atomic number is silicon's 14. -/
theorem center_atomicNumber :
    (source.molecule.atoms.get center.1).element.atomicNumber = 14 := by
  have h : center.1 = (0 : source.AromaticCanonicalAtom) := Fin.ext center_val
  rw [h]
  decide +kernel

/-- The actual recovered center is genuinely noncarbon. -/
theorem center_noncarbon : NoncarbonSemanticCenter source center.1 := by
  unfold NoncarbonSemanticCenter
  rw [center_atomicNumber]
  exact noncarbonCentralAtomicNumber_silicon_true

/-- The actual official CIP child IDs at the silicon center. -/
theorem official_root_ids :
    officialRootIDs source center.1 = [some 1, some 2, some 3, some 4] := by
  decide +kernel

/-- Every returned occurrence root list at the silicon center is a permutation of the actual IDs. -/
theorem root_ids_perm (fuel : Nat) :
    (finalOccurrenceRootIDs source fuel center).Perm [some 1, some 2, some 3, some 4] := by
  have binding := finalOccurrenceRootIDs_perm_officialRootIDs source fuel center
  rw [official_root_ids] at binding
  exact binding

noncomputable def target (fuel : Nat) : source.AromaticCanonicalOccurrence fuel :=
  source.aromaticCanonicalFinalOccurrence fuel center

/-- The noncarbon alignment genuinely succeeds at the silicon center, from the actual raw written
frame and the actual returned cursor IDs. -/
theorem alignment_exists (fuel : Nat) :
    ∃ slots, noncarbonParserSlotAlignment? raw source raw_toSemanticMolecule (target fuel) =
      some slots := by
  have recovered : source.aromaticCanonicalOccurrenceTetrahedralCenter? (target fuel) = some center := by
    unfold target
    exact occurrenceTetrahedralCenter?_final source fuel center
  have frames : source.aromaticCanonicalOccurrenceLigandFrame? (target fuel) =
      some (finalOccurrenceRoots source fuel center) := by
    unfold target
    exact finalOccurrenceRoots_are_returned source fuel center
  have idx : (parserIndexViaConversion raw source raw_toSemanticMolecule center).val = 0 := by
    rw [parserIndexViaConversion_val]
    rfl
  have endpoints : rawWrittenLigandFrame raw
      (parserIndexViaConversion raw source raw_toSemanticMolecule center) = [1, 2, 3, 4] := by
    unfold rawWrittenLigandFrame
    rw [idx]
    exact raw_written_endpoints
  have sameIDs :
      (occurrenceRootIDs source (finalOccurrenceRoots source fuel center)).Perm
        ([1, 2, 3, 4].map some) := by
    have rootPerm := root_ids_perm fuel
    simpa [occurrenceRootIDs, finalOccurrenceRootIDs] using rootPerm
  obtain ⟨positions, found⟩ := findSlotAlignment?_exists_of_perm [1, 2, 3, 4] _
    (by decide) (by decide) sameIDs
  refine ⟨positions, ?_⟩
  simp [noncarbonParserSlotAlignment?, recovered, center_noncarbon, frames, endpoints, found]

/-- Every successful closed silicon alignment has the complete noncarbon source-bound meaning. -/
theorem alignment_meaning (fuel : Nat) (slots : List Nat)
    (computed : noncarbonParserSlotAlignment? raw source raw_toSemanticMolecule (target fuel) =
      some slots) :
    ∃ center' roots, NoncarbonParserWrittenAlignment raw source raw_toSemanticMolecule
      raw_writtenExact (target fuel) center' roots slots :=
  noncarbonParserSlotAlignment?_sound raw source raw_toSemanticMolecule raw_writtenExact
    (target fuel) slots computed

/-- Any label the noncarbon parser channel returns for the closed silicon source is independently
meaningful, with the actual noncarbon center retained.  Success is not asserted. -/
theorem returned_label_meaning (fuel ruleFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (target fuel))
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : noncarbonParserDescriptor? raw source source_annotationAgreement raw_writtenExact
      (target fuel) view ruleFuel = some descriptor) :
    NoncarbonParserDescriptorMeaning raw source source_annotationAgreement raw_writtenExact
      (target fuel) view ruleFuel descriptor :=
  noncarbonParserDescriptor?_sound raw source source_annotationAgreement raw_writtenExact
    (target fuel) view ruleFuel descriptor computed

/-! ### Actual silicon key construction, strict ordering and emitted descriptor -/

/-- The parsed output of the repaired, hydrogen-frozen P-93 entry point is the closed source record
with every atom's hydrogen policy replaced by its exact source count.  This is *not* the literal
source record: the entry point materializes the source hydrogen policy, so the four-coordinate
silicon and the four monovalent halogens all store `explicitHydrogens? = some 0` where `raw` stores
`none`.  The counted value is derived (`RawMolecule.hydrogenCountAt`) from the written source graph
by the shared `RawSourceHydrogenPolicy` API; it is not assumed.  `p93_parsed_ne_raw` records that
the pre-repair literal identity no longer holds. -/
theorem p93_parsed_eq_raw :
    (normalizeRawMoleculeP93 raw []).parsed = RawMolecule.freezeSourceHydrogenCounts raw := by
  decide +kernel

/-- The pre-repair literal identity `parsed = raw` is false under the repaired pipeline: freezing
writes the stored hydrogen policy at every atom even when the counted value is zero. -/
theorem p93_parsed_ne_raw : (normalizeRawMoleculeP93 raw []).parsed ≠ raw := by
  decide +kernel

noncomputable def roots : List (source.AromaticCanonicalRerootCursor 0) :=
  finalOccurrenceRoots source 0 center

noncomputable def frame : source.AromaticCanonicalOccurrenceFourLigandFrame 0 :=
  { roots := roots, rootsLength := by rfl }

theorem roots_returned :
    source.aromaticCanonicalOccurrenceLigandFrame? (target 0) = some frame.roots :=
  finalOccurrenceRoots_are_returned source 0 center

theorem roots_real : OccurrenceRootsReal source frame := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

def atomicPriorityValue : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 35
  | ⟨3, _⟩ => 53

theorem actual_atomic_priority (slot : Fin 4) :
    occurrenceAtomicPriority source frame slot = atomicPriorityValue slot := by
  fin_cases slot <;> rfl

theorem actual_atomic_priority_injective :
    Function.Injective (occurrenceAtomicPriority source frame) := by
  have injective : Function.Injective atomicPriorityValue := by decide +kernel
  intro left right equal
  apply injective
  simpa only [actual_atomic_priority] using equal

theorem actual_priority_order_unique (order : List (Fin 4))
    (perm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      occurrenceAtomicPriority source frame right < occurrenceAtomicPriority source frame left)) :
    order = [3, 2, 1, 0] := by
  have reversedPerm : ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide +kernel
  have reversedDescending : ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      occurrenceAtomicPriority source frame right < occurrenceAtomicPriority source frame left) := by
    simp only [actual_atomic_priority]
    decide +kernel
  exact (perm.trans reversedPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    descending reversedDescending

theorem no_ordinary_double_bond : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : source.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

theorem parser_index_identity :
    (parserIndexViaConversion raw source raw_toSemanticMolecule center).val = 0 := rfl

theorem raw_frame :
    rawWrittenLigandFrame raw (parserIndexViaConversion raw source raw_toSemanticMolecule center) =
      [1, 2, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [parser_index_identity]
  exact raw_written_endpoints

theorem returned_root_ids : occurrenceRootIDs source roots = [some 1, some 2, some 3, some 4] := by
  rfl

theorem slot_alignment :
    findSlotAlignment?
      (rawWrittenLigandFrame raw (parserIndexViaConversion raw source raw_toSemanticMolecule center))
      (occurrenceRootIDs source roots) = some [0, 1, 2, 3] := by
  rw [raw_frame, returned_root_ids]
  decide +kernel

theorem raw_center_atom : raw.atomAt? 0 =
    some { AtomSpec.aliphatic .Si with tetrahedral? := some TetrahedralInputParity.clockwise } := rfl

/-- Actual silicon parser emission at carrier zero and sufficient rule fuel, for every dependency
view of this source. Keys and safe order are derived, never supplied as hypotheses. -/
theorem parser_descriptor_R (view : source.AromaticCanonicalDependencyView (target 0)) :
    noncarbonParserDescriptor? raw source source_annotationAgreement raw_writtenExact
      (target 0) view 2 = some (.chiral RS.R) := by
  obtain ⟨keys, tracked, keysComputed, trackedComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order source (target 0) view frame
      roots_returned roots_real actual_atomic_priority_injective no_ordinary_double_bond
  have keysComputed2 : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      (target 0) view 2 roots = some keys := keysComputed
  have orderEq := actual_priority_order_unique tracked.highestFirst perm descending
  have writtenOrder : tracked.highestFirst.map
      (fun position => ([0, 1, 2, 3] : List Nat).getD position.val 0) = [3, 2, 1, 0] := by
    rw [orderEq]
    rfl
  have rawEq := writtenFramePriorityDescriptor_clockwise_reverse [0, 1, 2, 3]
    tracked.highestFirst writtenOrder
  have recovered : source.aromaticCanonicalOccurrenceTetrahedralCenter? (target 0) = some center :=
    occurrenceTetrahedralCenter?_final source 0 center
  have evidenceComputed : constitutionParserRichPriorityEvidence? raw source
      source_annotationAgreement raw_writtenExact (target 0) view 2 =
      some
        ({ slots := [0, 1, 2, 3]
           keys := keys
           tracked := tracked
           writtenParity := .clockwise
           raw := RS.R } : ParserRichPriorityEvidence source 0) := by
    simp [constitutionParserRichPriorityEvidence?, recovered,
      parser_index_identity, raw_center_atom, roots_returned, frame,
      slot_alignment, keysComputed2, trackedComputed, rawEq]
  simp [noncarbonParserDescriptor?, recovered, center_noncarbon,
    constitutionParserRichDescriptor?, evidenceComputed, zero, classifyTetrahedralRSPseudo_zero]

/-- The actual emitted silicon label has this source's own complete independent meaning. -/
theorem parser_descriptor_R_meaning (view : source.AromaticCanonicalDependencyView (target 0)) :
    NoncarbonParserDescriptorMeaning raw source source_annotationAgreement raw_writtenExact
      (target 0) view 2 (.chiral RS.R) :=
  noncarbonParserDescriptor?_sound raw source source_annotationAgreement raw_writtenExact
    (target 0) view 2 (.chiral RS.R) (parser_descriptor_R view)

/-! ### Actual written-endpoint mismatch execution -/

/-- Same materialized molecule and annotation, but an invalid written frame substitutes the center
for ligand 4. The conversion-only alignment API must independently refuse the endpoint mismatch. -/
def mismatchedRaw : RawMolecule := { raw with neighborOrder := [[1, 2, 3, 0]] }

theorem mismatchedRaw_conversion : mismatchedRaw.toSemanticMolecule? = some source.molecule := by
  decide +kernel

/-- Actual matcher refusal, with no fabricated written-exact certificate or physical phantom. -/
theorem mismatched_alignment_none :
    noncarbonParserSlotAlignment? mismatchedRaw source mismatchedRaw_conversion (target 0) = none := by
  have recovered : source.aromaticCanonicalOccurrenceTetrahedralCenter? (target 0) = some center :=
    occurrenceTetrahedralCenter?_final source 0 center
  have badFrame : rawWrittenLigandFrame mismatchedRaw
      (parserIndexViaConversion mismatchedRaw source mismatchedRaw_conversion center) = [1, 2, 3, 0] :=
    rfl
  have mismatch : findSlotAlignment? [1, 2, 3, 0] [some 1, some 2, some 3, some 4] = none := by
    decide +kernel
  simp [noncarbonParserSlotAlignment?, recovered, center_noncarbon, roots_returned,
    frame, badFrame, returned_root_ids, mismatch]

/-- The committed carbon `CFClBrI` witness center has atomic number 6. -/
theorem carbon_witness_center_atomicNumber :
    (parserSource.molecule.atoms.get parserCenter.1).element.atomicNumber = 6 := by
  decide +kernel

/-- The committed carbon source is **not** silently relabelled noncarbon: its own center fails the
atom-specific comparator. -/
theorem carbon_witness_not_eligible : ¬ NoncarbonSemanticCenter parserSource parserCenter.1 := by
  unfold NoncarbonSemanticCenter
  rw [carbon_witness_center_atomicNumber]
  exact noncarbonCentralAtomicNumber_carbon_false

/-- The closed silicon source is genuinely noncarbon while the committed carbon witness is not. -/
theorem closed_silicon_is_genuine_noncarbon :
    NoncarbonSemanticCenter source center.1 ∧
      ¬ NoncarbonSemanticCenter parserSource parserCenter.1 :=
  ⟨center_noncarbon, carbon_witness_not_eligible⟩

/-- A four-real noncarbon success (silicon) is reported separately from the three-real-plus-lone-pair
refusal; the refusal is a boundary statement, not a general lone-pair capability claim. -/
theorem closed_silicon_fourReal_success_separate :
    (molecule.atoms.get center.1).element.atomicNumber = 14 ∧
      (raw.writtenNeighbors 0).length = 4 ∧
        ¬ NoncarbonSemanticCenter parserSource parserCenter.1 :=
  ⟨center_atomicNumber, by rw [raw_written_endpoints]; rfl, carbon_witness_not_eligible⟩

end ClosedSiliconTetrahedral

/-! ## 9. Kernel-authority guards for every exported declaration -/

assert_kernel_only NoncarbonCentralAtomicNumber
assert_kernel_only noncarbonCentralAtomicNumber_carbon_false
assert_kernel_only noncarbonCentralAtomicNumber_silicon_true
assert_kernel_only NoncarbonSemanticCenter
assert_kernel_only normalize_preserves_center_frame
assert_kernel_only normalize_preserves_center_atomicNumber
assert_kernel_only rawWrittenLigandFrame_normalize
assert_kernel_only NoncarbonParserWrittenAlignment
assert_kernel_only noncarbonParserSlotAlignment?
assert_kernel_only noncarbonParserSlotAlignment?_sound
assert_kernel_only noncarbonParserWrittenAlignment_index_converted
assert_kernel_only noncarbonParserWrittenAlignment_rawWritten_eq_rootID
assert_kernel_only NoncarbonParserDescriptorMeaning
assert_kernel_only noncarbonParserDescriptor?
assert_kernel_only noncarbonParserDescriptor?_sound
assert_kernel_only normalizeUnspecifiedBonds_atomAt?
assert_kernel_only p93Parsed_atomAt?_eq
assert_kernel_only p93Parsed_preserves_center_frame
assert_kernel_only FourRealWrittenLigandFrame
assert_kernel_only lonePairFrame_not_fourReal
assert_kernel_only elementSupportsPhantom_silicon_false
assert_kernel_only silicon_writtenConfigurationFrame_unsupported
assert_kernel_only silicon_threeCoordinate_refused
assert_kernel_only phantom_production_eq
assert_kernel_only phantom_frame_certificate
assert_kernel_only phantom_sentinel_not_materialized
assert_kernel_only group14_atomicNumber_silicon
assert_kernel_only group14_atomicNumber_ne_carbon
assert_kernel_only silicon_is_p93_noncarbon
assert_kernel_only ClosedSiliconTetrahedral.siliconAtom
assert_kernel_only ClosedSiliconTetrahedral.fluorineAtom
assert_kernel_only ClosedSiliconTetrahedral.chlorineAtom
assert_kernel_only ClosedSiliconTetrahedral.bromineAtom
assert_kernel_only ClosedSiliconTetrahedral.iodineAtom
assert_kernel_only ClosedSiliconTetrahedral.molecule
assert_kernel_only ClosedSiliconTetrahedral.raw
assert_kernel_only ClosedSiliconTetrahedral.source
assert_kernel_only ClosedSiliconTetrahedral.raw_toSemanticMolecule
assert_kernel_only ClosedSiliconTetrahedral.raw_writtenExact
assert_kernel_only ClosedSiliconTetrahedral.raw_written_endpoints
assert_kernel_only ClosedSiliconTetrahedral.source_annotationAgreement
assert_kernel_only ClosedSiliconTetrahedral.center_neighbors
assert_kernel_only ClosedSiliconTetrahedral.center
assert_kernel_only ClosedSiliconTetrahedral.center_val
assert_kernel_only ClosedSiliconTetrahedral.center_atomicNumber
assert_kernel_only ClosedSiliconTetrahedral.center_noncarbon
assert_kernel_only ClosedSiliconTetrahedral.official_root_ids
assert_kernel_only ClosedSiliconTetrahedral.root_ids_perm
assert_kernel_only ClosedSiliconTetrahedral.target
assert_kernel_only ClosedSiliconTetrahedral.alignment_exists
assert_kernel_only ClosedSiliconTetrahedral.alignment_meaning
assert_kernel_only ClosedSiliconTetrahedral.returned_label_meaning
assert_kernel_only ClosedSiliconTetrahedral.p93_parsed_eq_raw
assert_kernel_only ClosedSiliconTetrahedral.p93_parsed_ne_raw
assert_kernel_only ClosedSiliconTetrahedral.roots
assert_kernel_only ClosedSiliconTetrahedral.frame
assert_kernel_only ClosedSiliconTetrahedral.roots_returned
assert_kernel_only ClosedSiliconTetrahedral.roots_real
assert_kernel_only ClosedSiliconTetrahedral.atomicPriorityValue
assert_kernel_only ClosedSiliconTetrahedral.actual_atomic_priority
assert_kernel_only ClosedSiliconTetrahedral.actual_atomic_priority_injective
assert_kernel_only ClosedSiliconTetrahedral.actual_priority_order_unique
assert_kernel_only ClosedSiliconTetrahedral.no_ordinary_double_bond
assert_kernel_only ClosedSiliconTetrahedral.parser_index_identity
assert_kernel_only ClosedSiliconTetrahedral.raw_frame
assert_kernel_only ClosedSiliconTetrahedral.returned_root_ids
assert_kernel_only ClosedSiliconTetrahedral.slot_alignment
assert_kernel_only ClosedSiliconTetrahedral.raw_center_atom
assert_kernel_only ClosedSiliconTetrahedral.parser_descriptor_R
assert_kernel_only ClosedSiliconTetrahedral.parser_descriptor_R_meaning
assert_kernel_only ClosedSiliconTetrahedral.mismatchedRaw
assert_kernel_only ClosedSiliconTetrahedral.mismatchedRaw_conversion
assert_kernel_only ClosedSiliconTetrahedral.mismatched_alignment_none
assert_kernel_only ClosedSiliconTetrahedral.carbon_witness_center_atomicNumber
assert_kernel_only ClosedSiliconTetrahedral.carbon_witness_not_eligible
assert_kernel_only ClosedSiliconTetrahedral.closed_silicon_is_genuine_noncarbon
assert_kernel_only ClosedSiliconTetrahedral.closed_silicon_fourReal_success_separate

end TetraStereo.UniversalProof.SourceNativeNoncarbonParserAlignmentProofs.SourceNativeNoncarbonParserAlignment
