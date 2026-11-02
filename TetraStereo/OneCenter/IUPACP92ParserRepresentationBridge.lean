import TetraStereo.OneCenter.IUPACNext54P92DigraphRule1aReviewedSemantics
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

/-!
# Constructive parser-to-P92 constitutional representation

The universal authority input is intentionally broader than `RawMolecule`.  This module proves
the useful direction instead: when a parser molecule is successfully embedded, has exact source
Rule-2 masses and unique classical covalent bond records, its actual production `MoleculeGraph`
is an exact `P92ClassicalConstitutionRepresents` witness.

No inverse encoder or admitted-domain totality is asserted.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

namespace ParsedBondKind

/-- Bond spellings whose semantic interaction is exactly the natural-number bond order consumed
by the current constitutional graph.  Unspecified and aromatic records require a separate
normalization theorem and are deliberately excluded here. -/
def P92ClassicalCovalent : ParsedBondKind → Prop
  | .single | .double | .triple | .up | .down => True
  | .unspecified | .aromatic => False

end ParsedBondKind

namespace RawMolecule

/-- Parser-side subdomain represented without loss by the current P-92 constitutional graph. -/
def P92ClassicalCovalent (molecule : RawMolecule) : Prop :=
  (∀ atom, atom ∈ molecule.atoms → atom.aromatic = false) ∧
    ∀ bond, bond ∈ molecule.bonds → ParsedBondKind.P92ClassicalCovalent bond.kind

/-- Reusable checked parser-ingestion package for the P-92 constitutional production family. -/
structure P92ParserRepresentationCertificate
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule) : Prop where
  embedded : molecule.toSemanticMolecule? = some source.molecule
  wellFormed : molecule.WellFormed
  bondRecordsUnique : molecule.BondRecordsUnique
  rule2MassesKnown : molecule.Rule2MassesKnown
  classicalCovalent : RawMolecule.P92ClassicalCovalent molecule

/-- The semantic interaction emitted for a supported raw bond is anchored to that exact graph
edge and exact production bond order. -/
theorem p92PairInteractionRepresents_toMoleculeGraph
    (molecule : RawMolecule)
    (wellFormed : molecule.WellFormed)
    (bondRecordsUnique : molecule.BondRecordsUnique)
    {bond : RawBond} (bondMember : bond ∈ molecule.bonds)
    (kindSupported : ParsedBondKind.P92ClassicalCovalent bond.kind)
    (left right : Fin molecule.atomCount)
    (connects : bond.connects left.val right.val = true) :
    P92PairInteractionRepresents molecule.toMoleculeGraph left right
      bond.toSemanticInteraction := by
  constructor
  · simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at connects
    rcases connects with ⟨source, target⟩ | ⟨source, target⟩
    · left
      simp [RawBond.toSemanticInteraction, source, target]
    · right
      simp [RawBond.toSemanticInteraction, source, target]
  · have orderExact := molecule.bondOrder_eq_kind_of_mem_connects
      wellFormed bondRecordsUnique bondMember connects
    change (bond.toSemanticInteraction).kind =
      .covalent (molecule.bondOrder left.val right.val)
    rw [orderExact]
    cases kind : bond.kind <;>
      simp [kind, ParsedBondKind.P92ClassicalCovalent,
        RawBond.toSemanticInteraction, ParsedBondKind.order] at kindSupported ⊢

/-- Pair representation of a converted raw bond recovers the raw unordered incidence. -/
theorem connects_of_p92PairInteractionRepresents
    (molecule : RawMolecule) {bond : RawBond}
    (left right : Fin molecule.atomCount)
    (represented : P92PairInteractionRepresents molecule.toMoleculeGraph left right
      bond.toSemanticInteraction) :
    bond.connects left.val right.val = true := by
  rcases represented.1 with forward | reverse
  · simp only [RawBond.toSemanticInteraction] at forward
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    have first := List.cons.inj forward
    have second := List.cons.inj first.2
    exact Or.inl ⟨first.1, second.1⟩
  · simp only [RawBond.toSemanticInteraction] at reverse
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    have first := List.cons.inj reverse
    have second := List.cons.inj first.2
    exact Or.inr ⟨first.1, second.1⟩

/-- Edge-key uniqueness makes the converted semantic interaction list occurrence-unique even
though directional and plain single-bond spellings share one semantic interaction kind. -/
theorem p92SemanticInteractions_nodup
    (molecule : RawMolecule)
    (bondRecordsUnique : molecule.BondRecordsUnique) :
    (molecule.bonds.map RawBond.toSemanticInteraction).Nodup := by
  have bondsNodup : molecule.bonds.Nodup :=
    bondRecordsUnique.of_map RawBond.edgeKey
  apply (List.nodup_map_iff_inj_on bondsNodup).mpr
  intro first firstMember second secondMember semanticEqual
  have participantsEqual :
      first.source = second.source ∧ first.target = second.target := by
    simpa [RawBond.toSemanticInteraction] using
      congrArg (fun interaction : SemanticInteraction => interaction.participants) semanticEqual
  apply molecule.bond_eq_of_mem_of_connects bondRecordsUnique firstMember secondMember
      (left := first.source) (right := first.target)
  · simp [RawBond.connects]
  · simp [RawBond.connects, participantsEqual.1, participantsEqual.2]

theorem p92ClassicalConstitution_bond_exact
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (interactionsExact :
      source.molecule.interactions = molecule.bonds.map RawBond.toSemanticInteraction)
    (wellFormed : molecule.WellFormed)
    (bondRecordsUnique : molecule.BondRecordsUnique)
    (classicalCovalent : RawMolecule.P92ClassicalCovalent molecule) :
    ∀ left right : Fin molecule.atomCount, left ≠ right →
      (0 < molecule.toMoleculeGraph.bond left right ↔
        ∃! interaction : SemanticInteraction,
          interaction ∈ source.molecule.interactions ∧
            P92PairInteractionRepresents molecule.toMoleculeGraph left right interaction) := by
  intro left right different
  have valuesDifferent : left.val ≠ right.val := by
    intro equal
    exact different (Fin.ext equal)
  change 0 < molecule.bondOrder left.val right.val ↔ _
  constructor
  · intro positive
    rcases (molecule.bondOrder_pos_iff_exists_bond valuesDifferent).mp positive with
      ⟨bond, bondMember, connects⟩
    refine ⟨bond.toSemanticInteraction, ?_, ?_⟩
    · constructor
      · rw [interactionsExact]
        exact List.mem_map.mpr ⟨bond, bondMember, rfl⟩
      · exact p92PairInteractionRepresents_toMoleculeGraph molecule wellFormed
          bondRecordsUnique bondMember (classicalCovalent.2 bond bondMember)
            left right connects
    · intro other otherEvidence
      rcases List.mem_map.mp (by simpa [interactionsExact] using otherEvidence.1) with
        ⟨otherBond, otherBondMember, otherExact⟩
      subst other
      have otherConnects := connects_of_p92PairInteractionRepresents molecule
        left right otherEvidence.2
      have bondsEqual := molecule.bond_eq_of_mem_of_connects bondRecordsUnique
        otherBondMember bondMember otherConnects connects
      rw [bondsEqual]
  · rintro ⟨interaction, ⟨interactionMember, represented⟩, _unique⟩
    rw [interactionsExact] at interactionMember
    rcases List.mem_map.mp interactionMember with ⟨bond, bondMember, rfl⟩
    exact (molecule.bondOrder_pos_iff_exists_bond valuesDifferent).mpr
      ⟨bond, bondMember,
        connects_of_p92PairInteractionRepresents molecule left right represented⟩

/-- Successful parser ingestion realizes the exact format-neutral P-92 constitutional relation
for the production molecular graph. -/
theorem p92ClassicalConstitutionRepresents_toMoleculeGraph
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (embedded : molecule.toSemanticMolecule? = some source.molecule)
    (wellFormed : molecule.WellFormed)
    (bondRecordsUnique : molecule.BondRecordsUnique)
    (rule2MassesKnown : molecule.Rule2MassesKnown)
    (classicalCovalent : RawMolecule.P92ClassicalCovalent molecule) :
    P92ClassicalConstitutionRepresents source molecule.toMoleculeGraph := by
  have interactionsExact :=
    molecule.toSemanticMolecule?_interactions source.molecule embedded
  refine
    { atomCount_exact := molecule.toSemanticMolecule?_atomCount source.molecule embedded
      interaction_records_nodup := ?_
      atom_exact := ?_
      interaction_supported := ?_
      bond_exact := ?_ }
  · rw [interactionsExact]
    exact p92SemanticInteractions_nodup molecule bondRecordsUnique
  · intro atom
    let rawIndex : Fin molecule.atoms.length :=
      ⟨atom.val, by simp [RawMolecule.atomCount]⟩
    rcases molecule.toSemanticMolecule?_atomAtFin source.molecule embedded atom with
      ⟨sourceAtom, sourceLookup, atomConverted⟩
    have atomData := AtomSpec.toSemanticAtom?_exact
      (molecule.atoms.get rawIndex) sourceAtom atomConverted
    have atomMember : molecule.atoms.get rawIndex ∈ molecule.atoms :=
      List.get_mem molecule.atoms rawIndex
    have rawLookup :
        molecule.atomAt? atom.val = some (molecule.atoms.get rawIndex) := by
      simpa [RawMolecule.atomAt?, rawIndex] using
        (listGet?_eq_some_get molecule.atoms rawIndex)
    rcases molecule.atomMassAt_eq_of_rule2MassesKnown rule2MassesKnown atom.val
        (molecule.atoms.get rawIndex) rawLookup with
      ⟨mass, rawMassLookup, productionMass⟩
    have elementKnown : (molecule.atoms.get rawIndex).element ≠ .wildcard := by
      apply (AtomSpec.toSemanticAtom?_isSome (molecule.atoms.get rawIndex)).mp
      rw [atomConverted]
      rfl
    have authorityMassLookup :
        CIPRule2MassData.rule2MassPico?
            (molecule.atoms.get rawIndex).element.atomicNumber
            (molecule.atoms.get rawIndex).isotope? = some mass := by
      unfold RawMolecule.rule2MassPico? at rawMassLookup
      rw [if_neg elementKnown] at rawMassLookup
      exact rawMassLookup
    refine ⟨sourceAtom, sourceLookup, atomData.1.symm, mass, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [atomData.1, atomData.2.1] using authorityMassLookup
    · exact productionMass
    · exact atomData.2.2.1.symm
    · exact atomData.2.2.2.1
    · exact atomData.2.2.2.2.trans (classicalCovalent.1 _ atomMember)
  · intro interaction interactionMember
    rw [interactionsExact] at interactionMember
    rcases List.mem_map.mp interactionMember with ⟨bond, bondMember, rfl⟩
    have endpoints := wellFormed bond bondMember
    let left : Fin molecule.atomCount := ⟨bond.source, endpoints.1⟩
    let right : Fin molecule.atomCount := ⟨bond.target, endpoints.2.1⟩
    have connects : bond.connects left.val right.val = true := by
      simp [RawBond.connects, left, right]
    have orderExact := molecule.bondOrder_eq_kind_of_mem_connects
      wellFormed bondRecordsUnique bondMember connects
    refine ⟨left, right, ?_, ?_, ?_⟩
    · intro equal
      exact endpoints.2.2 (congrArg Fin.val equal)
    · change 0 < molecule.bondOrder left.val right.val
      rw [orderExact]
      cases bond.kind <;> decide
    · exact p92PairInteractionRepresents_toMoleculeGraph molecule wellFormed
        bondRecordsUnique bondMember (classicalCovalent.2 bond bondMember) left right connects
  · exact p92ClassicalConstitution_bond_exact molecule source interactionsExact
      wellFormed bondRecordsUnique classicalCovalent

/-! ## Transport to the production hierarchy graph -/

/-- Exact bond realization transports pointwise with the graph bond matrix. -/
theorem p92ClassicalConstitution_bond_exact_transport
    {source : AuthoritativeChemicalInput} {atomCount : Nat}
    {left right : MoleculeGraph (Fin atomCount)}
    (represented : P92ClassicalConstitutionRepresents source left)
    (bondExact : ∀ first second, right.bond first second = left.bond first second) :
    ∀ first second, first ≠ second →
      (0 < right.bond first second ↔
        ∃! interaction : SemanticInteraction,
          interaction ∈ source.molecule.interactions ∧
            P92PairInteractionRepresents right first second interaction) := by
  intro first second different
  simpa [P92PairInteractionRepresents, bondExact first second] using
    represented.bond_exact first second different

/-- Exact P-92 representation is invariant under pointwise equality of every graph datum used by
the reference relation.  This isolates normalization transport from parser ingestion. -/
theorem p92ClassicalConstitutionRepresents_transportGraph
    {source : AuthoritativeChemicalInput} {atomCount : Nat}
    {left right : MoleculeGraph (Fin atomCount)}
    (represented : P92ClassicalConstitutionRepresents source left)
    (atomZExact : ∀ atom, right.atomZ atom = left.atomZ atom)
    (atomMassExact : ∀ atom, right.atomMass atom = left.atomMass atom)
    (formalChargeExact : ∀ atom, right.formalCharge atom = left.formalCharge atom)
    (bondExact : ∀ first second, right.bond first second = left.bond first second) :
    P92ClassicalConstitutionRepresents source right := by
  refine
    { atomCount_exact := represented.atomCount_exact
      interaction_records_nodup := represented.interaction_records_nodup
      atom_exact := ?_
      interaction_supported := ?_
      bond_exact := ?_ }
  · intro atom
    rcases represented.atom_exact atom with ⟨sourceAtom, sourceLookup, atomRepresented⟩
    refine ⟨sourceAtom, sourceLookup, ?_⟩
    rcases atomRepresented with
      ⟨atomicNumber, mass, massLookup, productionMass, charge, unpaired, aromatic⟩
    exact ⟨(atomZExact atom).trans atomicNumber, mass, massLookup,
      (atomMassExact atom).trans productionMass,
      (formalChargeExact atom).trans charge, unpaired, aromatic⟩
  · intro interaction interactionMember
    rcases represented.interaction_supported interaction interactionMember with
      ⟨first, second, different, positive, pair⟩
    refine ⟨first, second, different, ?_, pair.1, ?_⟩
    · simpa [bondExact first second] using positive
    · exact pair.2.trans (congrArg SemanticInteractionKind.covalent
        (bondExact first second).symm)
  · exact p92ClassicalConstitution_bond_exact_transport represented bondExact

/-- Atomic-number form of the P/S center predicate used by the independent graph normalizer. -/
theorem element_atomicNumber_eq_phosphorus_or_sulfur_iff (element : Element) :
    (element.atomicNumber = 15 ∨ element.atomicNumber = 16) ↔
      (element = .P ∨ element = .S) := by
  cases element <;> decide

/-- Atomic-number form of the oxido ligand predicate. -/
theorem element_atomicNumber_eq_oxygen_iff (element : Element) :
    element.atomicNumber = 8 ↔ element = .O := by
  cases element <;> decide

/-- The production detector is exactly the independent graph-level oxido-root predicate on the
parser's constitutional graph. -/
theorem p92OxidoRootEligible_toMoleculeGraph_iff
    (molecule : RawMolecule) (center ligand : Fin molecule.atomCount) :
    P92OxidoRootEligible molecule.toMoleculeGraph center ligand ↔
      molecule.isTrigonalPyramidalOxidoRootEdge center ligand = true := by
  let centerIndex : Fin molecule.atoms.length :=
    ⟨center.val, by simp [RawMolecule.atomCount]⟩
  let ligandIndex : Fin molecule.atoms.length :=
    ⟨ligand.val, by simp [RawMolecule.atomCount]⟩
  have centerLookup :
      molecule.atomAt? center.val = some (molecule.atoms.get centerIndex) := by
    simpa [RawMolecule.atomAt?, centerIndex] using
      (listGet?_eq_some_get molecule.atoms centerIndex)
  have ligandLookup :
      molecule.atomAt? ligand.val = some (molecule.atoms.get ligandIndex) := by
    simpa [RawMolecule.atomAt?, ligandIndex] using
      (listGet?_eq_some_get molecule.atoms ligandIndex)
  unfold RawMolecule.isTrigonalPyramidalOxidoRootEdge
  rw [centerLookup, ligandLookup]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  change
    (((molecule.atoms.get centerIndex).element.atomicNumber = 15 ∨
        (molecule.atoms.get centerIndex).element.atomicNumber = 16) ∧
      (molecule.atoms.get ligandIndex).element.atomicNumber = 8 ∧
      molecule.bondOrder center.val ligand.val = 2) ↔ _
  rw [element_atomicNumber_eq_phosphorus_or_sulfur_iff,
    element_atomicNumber_eq_oxygen_iff]
  simp only [and_assoc]

/-- The production canonical-root bond function is extensionally identical to the independent
P-92 root normalization on the parser graph, including the P/S oxido case. -/
theorem canonicalHierarchyBond_eq_p92CanonicalRootBond
    (molecule : RawMolecule) (center ligand left right : Fin molecule.atomCount) :
    molecule.canonicalHierarchyBond center ligand left right =
      P92CanonicalRootBond molecule.toMoleculeGraph center ligand left right := by
  by_cases self : left = right
  · subst right
    simp [RawMolecule.canonicalHierarchyBond, P92CanonicalRootBond]
  · by_cases rootPair : P92RootPair center ligand left right
    · by_cases eligible : P92OxidoRootEligible molecule.toMoleculeGraph center ligand
      · have detected :=
          (p92OxidoRootEligible_toMoleculeGraph_iff molecule center ligand).mp eligible
        have valueDifferent : left.val ≠ right.val :=
          fun equal => self (Fin.ext equal)
        have rawRootPair :
            RawMolecule.IsRootPair center.val ligand.val left.val right.val := by
          simpa [P92RootPair, RawMolecule.IsRootPair, Fin.ext_iff] using rootPair
        simp [RawMolecule.canonicalHierarchyBond, P92CanonicalRootBond,
          self, valueDifferent, rootPair, rawRootPair,
          detected, eligible]
      · have notDetected :
          molecule.isTrigonalPyramidalOxidoRootEdge center ligand = false := by
          apply Bool.eq_false_iff.mpr
          intro detected
          exact eligible
            ((p92OxidoRootEligible_toMoleculeGraph_iff molecule center ligand).mpr detected)
        have valueDifferent : left.val ≠ right.val :=
          fun equal => self (Fin.ext equal)
        have rawRootPair :
            RawMolecule.IsRootPair center.val ligand.val left.val right.val := by
          simpa [P92RootPair, RawMolecule.IsRootPair, Fin.ext_iff] using rootPair
        simp [RawMolecule.canonicalHierarchyBond, P92CanonicalRootBond,
          self, valueDifferent, rootPair, rawRootPair,
          notDetected, eligible]
        rfl
    · have valueDifferent : left.val ≠ right.val :=
        fun equal => self (Fin.ext equal)
      have rawNotRootPair :
          ¬RawMolecule.IsRootPair center.val ligand.val left.val right.val := by
        simpa [P92RootPair, RawMolecule.IsRootPair, Fin.ext_iff] using rootPair
      simp [RawMolecule.canonicalHierarchyBond, P92CanonicalRootBond,
        self, valueDifferent, rootPair, rawNotRootPair]
      rfl

/-- Successful parser ingestion realizes the independently normalized canonical P-92 graph for
every root, including the source-authorized P/S oxido rewrite. -/
theorem p92CanonicalConstitutionRepresents_canonicalHierarchyMoleculeGraph
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (center ligand : Fin molecule.atomCount)
    (embedded : molecule.toSemanticMolecule? = some source.molecule)
    (wellFormed : molecule.WellFormed)
    (bondRecordsUnique : molecule.BondRecordsUnique)
    (rule2MassesKnown : molecule.Rule2MassesKnown)
    (classicalCovalent : RawMolecule.P92ClassicalCovalent molecule) :
    P92CanonicalConstitutionRepresents source center ligand
      (molecule.canonicalHierarchyMoleculeGraph center ligand) := by
  exact .intro molecule.toMoleculeGraph
    (p92ClassicalConstitutionRepresents_toMoleculeGraph molecule source embedded wellFormed
      bondRecordsUnique rule2MassesKnown classicalCovalent)
    (molecule.canonicalHierarchyMoleculeGraph_atomZ center ligand)
    (molecule.canonicalHierarchyMoleculeGraph_atomMass center ligand)
    (molecule.canonicalHierarchyMoleculeGraph_formalCharge center ligand)
    (canonicalHierarchyBond_eq_p92CanonicalRootBond molecule center ligand)

/-- Outside the one explicit oxido root-edge rewrite, the actual canonical hierarchy graph is an
exact representation of the same successfully embedded authority input. -/
theorem p92ClassicalConstitutionRepresents_canonicalHierarchyMoleculeGraph_of_not_oxido
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (center ligand : Fin molecule.atomCount)
    (embedded : molecule.toSemanticMolecule? = some source.molecule)
    (wellFormed : molecule.WellFormed)
    (bondRecordsUnique : molecule.BondRecordsUnique)
    (rule2MassesKnown : molecule.Rule2MassesKnown)
    (classicalCovalent : RawMolecule.P92ClassicalCovalent molecule)
    (notOxido : molecule.isTrigonalPyramidalOxidoRootEdge center ligand = false) :
    P92ClassicalConstitutionRepresents source
      (molecule.canonicalHierarchyMoleculeGraph center ligand) := by
  apply p92ClassicalConstitutionRepresents_transportGraph
    (p92ClassicalConstitutionRepresents_toMoleculeGraph molecule source embedded wellFormed
      bondRecordsUnique rule2MassesKnown classicalCovalent)
  · intro atom
    exact molecule.canonicalHierarchyMoleculeGraph_atomZ center ligand atom
  · intro atom
    exact molecule.canonicalHierarchyMoleculeGraph_atomMass center ligand atom
  · intro atom
    exact molecule.canonicalHierarchyMoleculeGraph_formalCharge center ligand atom
  · intro first second
    exact molecule.canonicalHierarchyMoleculeGraph_bond_eq_toMoleculeGraph_of_not_oxido
      center ligand first second notOxido

namespace P92ParserRepresentationCertificate

theorem representsToMoleculeGraph
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    (certificate : P92ParserRepresentationCertificate source molecule) :
    P92ClassicalConstitutionRepresents source molecule.toMoleculeGraph :=
  p92ClassicalConstitutionRepresents_toMoleculeGraph molecule source certificate.embedded
    certificate.wellFormed certificate.bondRecordsUnique certificate.rule2MassesKnown
      certificate.classicalCovalent

theorem representsCanonicalHierarchyExactOfNotOxido
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    (certificate : P92ParserRepresentationCertificate source molecule)
    (center ligand : Fin molecule.atomCount)
    (notOxido : molecule.isTrigonalPyramidalOxidoRootEdge center ligand = false) :
    P92ClassicalConstitutionRepresents source
      (molecule.canonicalHierarchyMoleculeGraph center ligand) :=
  p92ClassicalConstitutionRepresents_canonicalHierarchyMoleculeGraph_of_not_oxido molecule
    source center ligand certificate.embedded certificate.wellFormed
      certificate.bondRecordsUnique certificate.rule2MassesKnown certificate.classicalCovalent
        notOxido

theorem representsCanonicalHierarchy
    {source : AuthoritativeChemicalInput} {molecule : RawMolecule}
    (certificate : P92ParserRepresentationCertificate source molecule)
    (center ligand : Fin molecule.atomCount) :
    P92CanonicalConstitutionRepresents source center ligand
      (molecule.canonicalHierarchyMoleculeGraph center ligand) :=
  p92CanonicalConstitutionRepresents_canonicalHierarchyMoleculeGraph molecule source center ligand
    certificate.embedded certificate.wellFormed certificate.bondRecordsUnique
      certificate.rule2MassesKnown certificate.classicalCovalent

end P92ParserRepresentationCertificate

end RawMolecule

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.RawMolecule.p92ClassicalConstitutionRepresents_toMoleculeGraph
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.RawMolecule.p92ClassicalConstitutionRepresents_transportGraph
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.RawMolecule.p92ClassicalConstitutionRepresents_canonicalHierarchyMoleculeGraph_of_not_oxido
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.RawMolecule.canonicalHierarchyBond_eq_p92CanonicalRootBond
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.RawMolecule.p92CanonicalConstitutionRepresents_canonicalHierarchyMoleculeGraph
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.RawMolecule.P92ParserRepresentationCertificate.representsCanonicalHierarchy
