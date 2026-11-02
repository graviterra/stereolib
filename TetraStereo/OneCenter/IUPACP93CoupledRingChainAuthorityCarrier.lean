import TetraStereo.OneCenter.IUPACP93AcyclicAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93MonocyclicAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93FusedAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93CyclophaneAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93RingAssemblyAuthorityCarrier

set_option autoImplicit false

/-!
# Authority carrier for P-93.6 compounds composed of rings and chains

The exact constitutional name printed in the reviewed P-93.6 example is frozen together with its
source constitution before P-9 descriptors are attached.  This carrier intentionally does not
claim that a formal P-1--P-8 name generator has been executed: no such generator is part of the
current theory.  Descriptor values are projected from already reviewed family-specific authority
observations. For multiplicative names, concrete repeated-component atom carriers are related by
bijections preserving atom records and every internal interaction; actual descriptor assignments
are transported across those correspondences and compared.
-/

namespace TetraStereo.OneCenter

structure P93RingChainBaseName where
  tokens : List String
  deriving DecidableEq, Repr

def P93RingChainBaseName.Valid (name : P93RingChainBaseName) : Prop :=
  name.tokens ≠ []

/-- A reviewed printed-base-name certificate for one exact semantic constitution.  It records the
name/constitution pair transcribed from the normative example; the surrounding canonical source
transcription supplies the frozen artifact hash and PDF page.  It is deliberately narrower than
a correctness theorem for constitutional-name construction. -/
structure P93RingChainReviewedBaseNameCertificate where
  frozenName : P93RingChainBaseName
  frozenAtoms : List SemanticAtom
  frozenInteractions : List SemanticInteraction
  deriving DecidableEq, Repr

def P93RingChainReviewedBaseNameCertificate.ValidFor
    (source : AuthoritativeChemicalInput) (name : P93RingChainBaseName)
    (certificate : P93RingChainReviewedBaseNameCertificate) : Prop :=
  name.Valid ∧ source.StructurallyWellFormed ∧
    certificate.frozenName = name ∧
    certificate.frozenAtoms = source.molecule.atoms ∧
    certificate.frozenInteractions = source.molecule.interactions

theorem P93RingChainReviewedBaseNameCertificate.name_eq_of_validFor
    {source : AuthoritativeChemicalInput} {left right : P93RingChainBaseName}
    {certificate : P93RingChainReviewedBaseNameCertificate}
    (leftValid : certificate.ValidFor source left)
    (rightValid : certificate.ValidFor source right) : left = right := by
  exact leftValid.2.2.1.symm.trans rightValid.2.2.1

/-- One reviewed certificate cannot be transported between constitutionally different sources. -/
theorem P93RingChainReviewedBaseNameCertificate.constitution_eq_of_validFor
    {leftSource rightSource : AuthoritativeChemicalInput} {name : P93RingChainBaseName}
    {certificate : P93RingChainReviewedBaseNameCertificate}
    (leftValid : certificate.ValidFor leftSource name)
    (rightValid : certificate.ValidFor rightSource name) :
    leftSource.molecule.atoms = rightSource.molecule.atoms ∧
      leftSource.molecule.interactions = rightSource.molecule.interactions := by
  exact ⟨leftValid.2.2.2.1.symm.trans rightValid.2.2.2.1,
    leftValid.2.2.2.2.symm.trans rightValid.2.2.2.2⟩

inductive P93RingChainStereogenicUnit where
  | center (atom : Nat)
  | doubleBond (first second : Nat)
  | cumuleneAxis (path : List Nat)
  | bondAxis (first second : Nat)
  | fusedAxis (path : List Nat)
  | plane (members : Finset Nat)
  | helix (path : List Nat)
  | polyhedron (center : Nat) (positions : Finset Nat)
  deriving DecidableEq

def P93RingChainStereogenicUnit.ofAuthorityPhysical :
    P93AuthorityPhysicalUnit → P93RingChainStereogenicUnit
  | .atomCenter atom => .center atom
  | .bond first second => .doubleBond first second
  | .axis path => .cumuleneAxis path
  | .plane members => .plane members
  | .helix path => .helix path
  | .polyhedron centerAtom positions => .polyhedron centerAtom positions

def P93RingChainStereogenicUnit.atoms :
    P93RingChainStereogenicUnit → Finset Nat
  | .center atom => {atom}
  | .doubleBond first second
  | .bondAxis first second => {first, second}
  | .cumuleneAxis path
  | .fusedAxis path
  | .helix path => path.toFinset
  | .plane members => members
  | .polyhedron centerAtom positions => insert centerAtom positions

inductive P93RingChainDescriptor where
  | acyclic (descriptor : BlueBookP93.Acyclic.Descriptor)
  | fused (descriptor : BlueBookP93.Cyclic.FusedUnitDescriptor)
  | cyclophanePlane (descriptor : BlueBookP93.Cyclic.CyclophanePlaneDescriptor)
  | cyclophaneRelativeCenter (descriptor : BlueBookP93.Cyclic.RCTDescriptor)
  | polyhedral (descriptor : PolyhedralChiralitySymbol)
  | ringAssemblyAxis (descriptor : BlueBookP93.Cyclic.RingAssemblyAxisDescriptor)
  | ringAssemblyCenter (descriptor : BlueBookP93.Cyclic.RingAssemblyCenterDescriptor)
  deriving DecidableEq, Repr

structure P93CoupledRingChainDescriptorPolicies where
  acyclic : P93AcyclicAuthorityPolicy
  monocyclic : P93MonocyclicAuthorityPolicy
  fused : P93FusedAuthorityPolicy
  cyclophane : P93CyclophaneAuthorityPolicy
  spiro : P93SpiroAuthorityPolicy
  ringAssembly : P93RingAssemblyAuthorityPolicy

inductive P93RingChainReviewedDescriptorEvidence
    (policies : P93CoupledRingChainDescriptorPolicies) where
  | acyclicCenter
      (observation : P93AcyclicSingleCenterAuthorityObservation policies.acyclic)
  | acyclicDoubleBond
      (observation : P93AcyclicDoubleBondAuthorityObservation policies.acyclic)
  | acyclicEvenCumulene
      (observation : P93AcyclicEvenCumuleneAuthorityObservation policies.acyclic)
  | acyclicOddCumulene
      (observation : P93AcyclicOddCumuleneAuthorityObservation policies.acyclic)
  | monocyclicCenter
      (observation : P93MonocyclicCenterAuthorityObservation policies.monocyclic)
  | monocyclicDoubleBond
      (observation : P93MonocyclicDoubleBondAuthorityObservation policies.monocyclic)
      (citation : P93AuthorityCitationToken)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | fusedCIP
      (observation : P93FusedCIPAuthorityObservation policies.fused)
  | cyclophanePlane
      (observation : P93CyclophanePlaneAuthorityObservation policies.cyclophane)
  | cyclophaneCenterCIP
      (observation : P93CyclophaneCenterAuthorityObservation policies.cyclophane)
      (context : BlueBookP93.Acyclic.NomenclatureContext)
      (kind : BlueBookP93.Acyclic.UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | cyclophaneCenterRelative
      (observation : P93CyclophaneCenterAuthorityObservation policies.cyclophane)
      (assignment : P93CyclophaneRCTLocatedAssignment)
  | cyclophaneDoubleBond
      (observation : P93CyclophaneDoubleBondAuthorityObservation policies.cyclophane)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | spiroPolyhedral
      (observation : P93SpiroPolyhedralAuthorityObservation policies.spiro)
  | ringAssemblyAxis
      (observation : P93RingAssemblyAxesAuthorityObservation policies.ringAssembly)
      (assignment : P93RingAssemblyAxisAssignment)
  | ringAssemblyCenter
      (observation : P93RingAssemblyCentersAuthorityObservation policies.ringAssembly)
      (assignment : P93RingAssemblyCenterAssignment)
  | ringAssemblyDoubleBond
      (observation : P93RingAssemblyDoubleBondsAuthorityObservation policies.ringAssembly)
      (assignment : P93RingAssemblyDoubleBondAssignment)

def P93RingChainReviewedDescriptorEvidence.unit
    {policies : P93CoupledRingChainDescriptorPolicies} :
    P93RingChainReviewedDescriptorEvidence policies → P93RingChainStereogenicUnit
  | .acyclicCenter observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.assignment.unit
  | .acyclicDoubleBond observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.assignment.unit
  | .acyclicEvenCumulene observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.assignment.unit
  | .acyclicOddCumulene observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.assignment.unit
  | .monocyclicCenter observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.physical.unit
  | .monocyclicDoubleBond observation _ _ =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.physical.unit
  | .fusedCIP observation =>
      match observation.unit with
      | .physical unit => P93RingChainStereogenicUnit.ofAuthorityPhysical unit
      | .fusedAxis path => .fusedAxis path
  | .cyclophanePlane observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.unit
  | .cyclophaneCenterCIP observation _ _ _ =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.unit
  | .cyclophaneCenterRelative _ assignment => .center assignment.center
  | .cyclophaneDoubleBond observation _ =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.unit
  | .spiroPolyhedral observation =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical observation.unit
  | .ringAssemblyAxis _ assignment =>
      .bondAxis assignment.junction.leftAtom assignment.junction.rightAtom
  | .ringAssemblyCenter _ assignment => .center assignment.center
  | .ringAssemblyDoubleBond _ assignment =>
      .doubleBond assignment.first assignment.second

def P93RingChainReviewedDescriptorEvidence.citation?
    {policies : P93CoupledRingChainDescriptorPolicies} :
    P93RingChainReviewedDescriptorEvidence policies →
      Option P93AuthorityCitationToken
  | .acyclicCenter observation => observation.assignment.citation?
  | .acyclicDoubleBond observation => observation.assignment.citation?
  | .acyclicEvenCumulene observation => observation.assignment.citation?
  | .acyclicOddCumulene observation => observation.assignment.citation?
  | .monocyclicCenter observation => some observation.citation
  | .monocyclicDoubleBond _ citation _ => some citation
  /- Suffixed fused locants have no lossless representation in this legacy numeric channel. -/
  | .fusedCIP _ => none
  | .cyclophanePlane observation => some observation.citation
  | .cyclophaneCenterCIP observation _ _ _ => some observation.citation
  | .cyclophaneCenterRelative _ assignment => some assignment.citation
  | .cyclophaneDoubleBond observation _ => some observation.citation
  | .spiroPolyhedral observation => some observation.citation
  | .ringAssemblyAxis _ assignment => some assignment.citation
  | .ringAssemblyCenter _ assignment => some assignment.citation
  | .ringAssemblyDoubleBond _ assignment => some assignment.citation

def P93RingChainReviewedDescriptorEvidence.descriptor
    {policies : P93CoupledRingChainDescriptorPolicies} :
    P93RingChainReviewedDescriptorEvidence policies → P93RingChainDescriptor
  | .acyclicCenter observation => .acyclic observation.assignment.descriptor
  | .acyclicDoubleBond observation => .acyclic observation.assignment.descriptor
  | .acyclicEvenCumulene observation => .acyclic observation.assignment.descriptor
  | .acyclicOddCumulene observation => .acyclic observation.assignment.descriptor
  | .monocyclicCenter observation => .acyclic observation.descriptor
  | .monocyclicDoubleBond _ _ descriptor => .acyclic descriptor
  | .fusedCIP observation => .fused observation.descriptor
  | .cyclophanePlane observation => .cyclophanePlane observation.descriptor
  | .cyclophaneCenterCIP _ _ _ descriptor => .acyclic descriptor
  | .cyclophaneCenterRelative _ assignment =>
      .cyclophaneRelativeCenter assignment.descriptor
  | .cyclophaneDoubleBond _ descriptor => .acyclic descriptor
  | .spiroPolyhedral observation => .polyhedral observation.descriptor
  | .ringAssemblyAxis _ assignment => .ringAssemblyAxis assignment.preferredDescriptor
  | .ringAssemblyCenter _ assignment =>
      .ringAssemblyCenter assignment.preferredDescriptor
  | .ringAssemblyDoubleBond _ assignment => .acyclic assignment.descriptor

def P93RingChainReviewedDescriptorEvidence.ValidFor
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput) :
    P93RingChainReviewedDescriptorEvidence policies → Prop
  | .acyclicCenter observation => observation.ValidFor policies.acyclic source
  | .acyclicDoubleBond observation => observation.ValidFor policies.acyclic source
  | .acyclicEvenCumulene observation => observation.ValidFor policies.acyclic source
  | .acyclicOddCumulene observation => observation.ValidFor policies.acyclic source
  | .monocyclicCenter observation => observation.ValidFor policies.monocyclic source
  | .monocyclicDoubleBond observation citation descriptor =>
      observation.ValidFor policies.monocyclic source ∧
        observation.descriptor? = some descriptor ∧ citation.Valid
  | .fusedCIP observation => observation.ValidFor policies.fused source
  | .cyclophanePlane observation => observation.ValidFor policies.cyclophane source
  | .cyclophaneCenterCIP observation context kind descriptor =>
      observation.ValidFor policies.cyclophane source ∧
        observation.specification = .cip context kind descriptor
  | .cyclophaneCenterRelative observation assignment =>
      observation.ValidFor policies.cyclophane source ∧
        ∃ candidates selected referenceSide assignments,
          observation.specification =
            .relativeRCT candidates selected referenceSide assignments ∧
          assignment ∈ assignments
  | .cyclophaneDoubleBond observation descriptor =>
      observation.ValidFor policies.cyclophane source ∧
        observation.descriptor? = some descriptor
  | .spiroPolyhedral observation => observation.ValidFor policies.spiro source
  | .ringAssemblyAxis observation assignment =>
      observation.ValidFor policies.ringAssembly source ∧
        assignment ∈ observation.assignments
  | .ringAssemblyCenter observation assignment =>
      observation.ValidFor policies.ringAssembly source ∧
        assignment ∈ observation.assignments
  | .ringAssemblyDoubleBond observation assignment =>
      observation.ValidFor policies.ringAssembly source ∧
        assignment ∈ observation.assignments

structure P93RingChainDescriptorAssignment
    (policies : P93CoupledRingChainDescriptorPolicies) where
  evidence : P93RingChainReviewedDescriptorEvidence policies

def P93RingChainDescriptorAssignment.unit
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies) :
    P93RingChainStereogenicUnit := assignment.evidence.unit

def P93RingChainDescriptorAssignment.descriptor
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies) : P93RingChainDescriptor :=
  assignment.evidence.descriptor

inductive P93RingChainPhysicalIdentity where
  | center (atom : Nat)
  | bond (atoms : Finset Nat)
  | axis (atoms : Finset Nat)
  | plane (members : Finset Nat)
  | helix (atoms : Finset Nat)
  | polyhedron (center : Nat) (positions : Finset Nat)
  deriving DecidableEq

def P93RingChainStereogenicUnit.physicalIdentity :
    P93RingChainStereogenicUnit → P93RingChainPhysicalIdentity
  | .center atom => .center atom
  | .doubleBond first second
  | .bondAxis first second => .bond {first, second}
  | .cumuleneAxis path
  | .fusedAxis path => .axis path.toFinset
  | .plane members => .plane members
  | .helix path => .helix path.toFinset
  | .polyhedron centerAtom positions => .polyhedron centerAtom positions

structure P93RingChainRepeatedComponent where
  atoms : Finset Nat
  deriving DecidableEq

def P93RingChainRepeatedComponent.ValidFor
    (source : AuthoritativeChemicalInput)
    (component : P93RingChainRepeatedComponent) : Prop :=
  component.atoms.Nonempty ∧
    ∀ atom ∈ component.atoms, atom < source.molecule.atomCount

structure P93RingChainAssignmentOwnership where
  assignmentIndex : Nat
  componentIndex : Nat
  deriving DecidableEq, Repr

def P93RingChainAssignmentTouchesComponent
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies)
    (component : P93RingChainRepeatedComponent) : Prop :=
  ¬Disjoint assignment.unit.atoms component.atoms

def P93RingChainAssignmentOwnershipsComplete
    {policies : P93CoupledRingChainDescriptorPolicies}
    (components : List P93RingChainRepeatedComponent)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership) : Prop :=
  (ownerships.map fun ownership =>
      (ownership.assignmentIndex, ownership.componentIndex)).Nodup ∧
    (∀ ownership ∈ ownerships,
      ∃ assignment component,
        assignments[ownership.assignmentIndex]? = some assignment ∧
          components[ownership.componentIndex]? = some component ∧
          P93RingChainAssignmentTouchesComponent assignment component) ∧
    ∀ assignmentIndex assignment,
      assignments[assignmentIndex]? = some assignment →
        ∀ componentIndex component,
          components[componentIndex]? = some component →
            P93RingChainAssignmentTouchesComponent assignment component →
              ∃ ownership ∈ ownerships,
                ownership.assignmentIndex = assignmentIndex ∧
                  ownership.componentIndex = componentIndex

structure P93RingChainComponentCorrespondence where
  leftIndex : Nat
  rightIndex : Nat
  atomPairs : List (Nat × Nat)
  attachmentPairs : List (Nat × Nat)
  deriving DecidableEq, Repr

def P93RingChainAtomsCorrespond
    (correspondence : P93RingChainComponentCorrespondence)
    (left right : Nat) : Prop :=
  (left, right) ∈ correspondence.atomPairs ∨
    (left, right) ∈ correspondence.attachmentPairs

def P93RingChainFinsetsCorrespond
    (correspondence : P93RingChainComponentCorrespondence)
    (left right : Finset Nat) : Prop :=
  (∀ atom ∈ left, ∃ mapped ∈ right,
    P93RingChainAtomsCorrespond correspondence atom mapped) ∧
    ∀ mapped ∈ right, ∃ atom ∈ left,
      P93RingChainAtomsCorrespond correspondence atom mapped

def P93RingChainListsCorrespond
    (correspondence : P93RingChainComponentCorrespondence)
    (left right : List Nat) : Prop :=
  List.Forall₂ (P93RingChainAtomsCorrespond correspondence) left right ∨
    List.Forall₂ (P93RingChainAtomsCorrespond correspondence) left right.reverse

def P93RingChainUnitsCorrespond
    (correspondence : P93RingChainComponentCorrespondence) :
    P93RingChainStereogenicUnit → P93RingChainStereogenicUnit → Prop
  | .center left, .center right =>
      P93RingChainAtomsCorrespond correspondence left right
  | .doubleBond leftFirst leftSecond, .doubleBond rightFirst rightSecond
  | .bondAxis leftFirst leftSecond, .bondAxis rightFirst rightSecond =>
      (P93RingChainAtomsCorrespond correspondence leftFirst rightFirst ∧
        P93RingChainAtomsCorrespond correspondence leftSecond rightSecond) ∨
      (P93RingChainAtomsCorrespond correspondence leftFirst rightSecond ∧
        P93RingChainAtomsCorrespond correspondence leftSecond rightFirst)
  | .cumuleneAxis left, .cumuleneAxis right
  | .fusedAxis left, .fusedAxis right
  | .helix left, .helix right =>
      P93RingChainListsCorrespond correspondence left right
  | .plane left, .plane right =>
      P93RingChainFinsetsCorrespond correspondence left right
  | .polyhedron leftCenter leftPositions,
      .polyhedron rightCenter rightPositions =>
      P93RingChainAtomsCorrespond correspondence leftCenter rightCenter ∧
        P93RingChainFinsetsCorrespond correspondence leftPositions rightPositions
  | _, _ => False

def P93RingChainInteractionTouches
    (atoms : Finset Nat) (interaction : SemanticInteraction) : Prop :=
  ∃ atom ∈ interaction.participants, atom ∈ atoms

def P93RingChainAtomInOwnedBoundaryUnit
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex atom : Nat) : Prop :=
  ∃ ownership ∈ ownerships, ∃ assignment,
    ownership.componentIndex = componentIndex ∧
      assignments[ownership.assignmentIndex]? = some assignment ∧
      atom ∈ assignment.unit.atoms

def P93RingChainInterfaceAtom
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (_components : List P93RingChainRepeatedComponent)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex : Nat)
    (component : P93RingChainRepeatedComponent)
    (atom : Nat) : Prop :=
  atom ∉ component.atoms ∧
    ((∃ interaction ∈ source.molecule.interactions,
      P93RingChainInteractionTouches component.atoms interaction ∧
        atom ∈ interaction.participants) ∨
      P93RingChainAtomInOwnedBoundaryUnit assignments ownerships
        componentIndex atom)

def P93RingChainInteractionTouchesOwnedInterface
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex : Nat)
    (component : P93RingChainRepeatedComponent)
    (interaction : SemanticInteraction) : Prop :=
  (∀ atom ∈ interaction.participants,
    atom ∈ component.atoms ∨
      P93RingChainInterfaceAtom source components assignments ownerships
        componentIndex component atom) ∧
    ∃ atom ∈ interaction.participants,
      atom ∈ component.atoms ∨
        P93RingChainAtomInOwnedBoundaryUnit assignments ownerships
          componentIndex atom

def P93RingChainInteractionCorresponds
    (correspondence : P93RingChainComponentCorrespondence)
    (left right : SemanticInteraction) : Prop :=
  left.kind = right.kind ∧
    P93RingChainFinsetsCorrespond correspondence
      left.participants.toFinset right.participants.toFinset

def P93RingChainComponentCorrespondence.ValidFor
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership)
    (correspondence : P93RingChainComponentCorrespondence) : Prop :=
  correspondence.leftIndex = 0 ∧ 0 < correspondence.rightIndex ∧
    ∃ left right,
      components[correspondence.leftIndex]? = some left ∧
        components[correspondence.rightIndex]? = some right ∧
        (correspondence.atomPairs.map Prod.fst).Nodup ∧
        (correspondence.atomPairs.map Prod.snd).Nodup ∧
        (correspondence.attachmentPairs.map Prod.fst).Nodup ∧
        (correspondence.attachmentPairs.map Prod.snd).Nodup ∧
        (correspondence.atomPairs.map Prod.fst).toFinset = left.atoms ∧
        (correspondence.atomPairs.map Prod.snd).toFinset = right.atoms ∧
        (∀ atom,
          atom ∈ (correspondence.attachmentPairs.map Prod.fst).toFinset ↔
            P93RingChainInterfaceAtom source components assignments ownerships
              correspondence.leftIndex left atom) ∧
        (∀ atom,
          atom ∈ (correspondence.attachmentPairs.map Prod.snd).toFinset ↔
            P93RingChainInterfaceAtom source components assignments ownerships
              correspondence.rightIndex right atom) ∧
        (∀ leftAtom rightAtom,
          P93RingChainAtomsCorrespond correspondence leftAtom rightAtom →
            source.molecule.atoms[leftAtom]? = source.molecule.atoms[rightAtom]?) ∧
        (∀ leftInteraction ∈ source.molecule.interactions,
          P93RingChainInteractionTouchesOwnedInterface source components assignments
              ownerships correspondence.leftIndex left leftInteraction →
            ∃ rightInteraction ∈ source.molecule.interactions,
              P93RingChainInteractionTouchesOwnedInterface source components assignments
                  ownerships correspondence.rightIndex right rightInteraction ∧
                P93RingChainInteractionCorresponds correspondence
                  leftInteraction rightInteraction) ∧
        ∀ rightInteraction ∈ source.molecule.interactions,
          P93RingChainInteractionTouchesOwnedInterface source components assignments
              ownerships correspondence.rightIndex right rightInteraction →
            ∃ leftInteraction ∈ source.molecule.interactions,
              P93RingChainInteractionTouchesOwnedInterface source components assignments
                  ownerships correspondence.leftIndex left leftInteraction ∧
                P93RingChainInteractionCorresponds correspondence
                  leftInteraction rightInteraction

def P93RingChainAssignmentsStereoCorrespond
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership)
    (leftIndex rightIndex : Nat)
    (correspondence : P93RingChainComponentCorrespondence) : Prop :=
  (∀ ownership ∈ ownerships,
    ownership.componentIndex = leftIndex →
      ∀ assignment,
        assignments[ownership.assignmentIndex]? = some assignment →
          ∃ mappedOwnership ∈ ownerships, ∃ mapped,
            mappedOwnership.componentIndex = rightIndex ∧
              assignments[mappedOwnership.assignmentIndex]? = some mapped ∧
              P93RingChainUnitsCorrespond correspondence assignment.unit mapped.unit ∧
              assignment.descriptor = mapped.descriptor) ∧
    ∀ mappedOwnership ∈ ownerships,
      mappedOwnership.componentIndex = rightIndex →
        ∀ mapped,
          assignments[mappedOwnership.assignmentIndex]? = some mapped →
            ∃ ownership ∈ ownerships, ∃ assignment,
              ownership.componentIndex = leftIndex ∧
                assignments[ownership.assignmentIndex]? = some assignment ∧
                P93RingChainUnitsCorrespond correspondence assignment.unit mapped.unit ∧
                assignment.descriptor = mapped.descriptor

structure P93CoupledRingChainAuthorityPolicy where
  descriptorPolicies : P93CoupledRingChainDescriptorPolicies
  ReviewedBaseNameMatchesSource :
    AuthoritativeChemicalInput → P93RingChainBaseName → Prop
  StereogenicUnitEligible :
    AuthoritativeChemicalInput → P93RingChainBaseName →
      P93RingChainStereogenicUnit → Prop
  EvidenceBelongsToName :
    AuthoritativeChemicalInput → P93RingChainBaseName →
      P93RingChainReviewedDescriptorEvidence descriptorPolicies → Prop
  CitationConformsToBaseNumbering :
    AuthoritativeChemicalInput → P93RingChainBaseName →
      P93AuthorityCitationToken → P93RingChainStereogenicUnit → Prop
  RepeatedComponentsObserved :
    AuthoritativeChemicalInput → P93RingChainBaseName →
      List P93RingChainRepeatedComponent → Prop
  MultiplicativeNameSelected :
    AuthoritativeChemicalInput → P93RingChainBaseName → Prop

def P93RingChainDescriptorAssignment.ValidFor
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (baseName : P93RingChainBaseName)
    (assignment : P93RingChainDescriptorAssignment policy.descriptorPolicies) : Prop :=
  assignment.evidence.ValidFor source ∧
    policy.StereogenicUnitEligible source baseName assignment.unit ∧
    policy.EvidenceBelongsToName source baseName assignment.evidence ∧
    match assignment.evidence.citation? with
    | none => True
    | some citation =>
        citation.Valid ∧
          policy.CitationConformsToBaseNumbering source baseName citation assignment.unit

def P93RingChainRepeatedComponentsValid
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent) : Prop :=
  2 ≤ components.length ∧
    (components.map fun component => component.atoms).Nodup ∧
    (∀ component ∈ components, component.ValidFor source) ∧
    ∀ (leftIndex : Nat) (left : P93RingChainRepeatedComponent),
      components[leftIndex]? = some left →
      ∀ (rightIndex : Nat) (right : P93RingChainRepeatedComponent),
        components[rightIndex]? = some right →
        leftIndex ≠ rightIndex → Disjoint left.atoms right.atoms

/-- Number of atoms of one element in a repeated constitutional component. -/
def P93RingChainComponentElementCount
    (source : AuthoritativeChemicalInput)
    (component : P93RingChainRepeatedComponent) (atomicNumber : Nat) : Nat :=
  (component.atoms.filter fun atom =>
    source.molecule.atoms[atom]?.map (fun record => record.element.atomicNumber) =
      some atomicNumber).card

/-- A source-only obstruction to a constitution-preserving component bijection.  Either the
component cardinalities differ or one element multiplicity differs. -/
inductive P93RingChainComponentsConstitutionallyNonisomorphic
    (source : AuthoritativeChemicalInput)
    (left right : P93RingChainRepeatedComponent) : Prop where
  | atomCardinality
      (different : left.atoms.card ≠ right.atoms.card)
  | elementMultiplicity (atomicNumber : Nat)
      (different :
        P93RingChainComponentElementCount source left atomicNumber ≠
          P93RingChainComponentElementCount source right atomicNumber)

def P93RingChainOwnedDescriptorMismatch
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership) : Prop :=
  ∃ leftOwnership ∈ ownerships, ∃ rightOwnership ∈ ownerships,
    leftOwnership.componentIndex ≠ rightOwnership.componentIndex ∧
      ∃ leftAssignment rightAssignment,
        assignments[leftOwnership.assignmentIndex]? = some leftAssignment ∧
          assignments[rightOwnership.assignmentIndex]? = some rightAssignment ∧
          leftAssignment.descriptor ≠ rightAssignment.descriptor

/-- Evidence for rejecting multiplicative selection.  Rejection is substantive: ownership is
complete, an owned descriptor differs across components, and two owned repeated components are
provably constitutionally nonisomorphic. -/
structure P93RingChainMultiplicativeRejectionEvidence
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership) : Prop where
  componentsValid : P93RingChainRepeatedComponentsValid source components
  ownershipsComplete :
    P93RingChainAssignmentOwnershipsComplete components assignments ownerships
  descriptorMismatch : P93RingChainOwnedDescriptorMismatch assignments ownerships
  componentNonisomorphism :
    ∃ leftOwnership ∈ ownerships, ∃ rightOwnership ∈ ownerships,
      leftOwnership.componentIndex ≠ rightOwnership.componentIndex ∧
        ∃ leftComponent rightComponent,
          components[leftOwnership.componentIndex]? = some leftComponent ∧
            components[rightOwnership.componentIndex]? = some rightComponent ∧
            P93RingChainComponentsConstitutionallyNonisomorphic
              source leftComponent rightComponent

def P93RingChainMultiplicativeSymmetryComplete
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (correspondences : List P93RingChainComponentCorrespondence)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership) : Prop :=
  P93RingChainRepeatedComponentsValid source components ∧
    P93RingChainAssignmentOwnershipsComplete components assignments ownerships ∧
    (correspondences.map fun correspondence => correspondence.rightIndex).Nodup ∧
    (∀ correspondence ∈ correspondences,
      correspondence.ValidFor source components assignments ownerships ∧
        P93RingChainAssignmentsStereoCorrespond assignments ownerships
          correspondence.leftIndex correspondence.rightIndex correspondence) ∧
    ∀ index, 0 < index → index < components.length →
      ∃ correspondence ∈ correspondences,
        correspondence.rightIndex = index

/-- The two exhaustive proof branches for the printed multiplicative-name decision.  A selected
decision carries full constitutional/stereochemical symmetry; a rejected decision carries the
two independently checkable rejection reasons. -/
inductive P93RingChainMultiplicativeDecisionValid
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (correspondences : List P93RingChainComponentCorrespondence)
    (assignments : List (P93RingChainDescriptorAssignment policies))
    (ownerships : List P93RingChainAssignmentOwnership) : Bool → Prop where
  | selected
      (symmetryComplete : P93RingChainMultiplicativeSymmetryComplete source components
        correspondences assignments ownerships) :
      P93RingChainMultiplicativeDecisionValid source components correspondences
        assignments ownerships true
  | rejected
      (evidence : P93RingChainMultiplicativeRejectionEvidence source components
        assignments ownerships) :
      P93RingChainMultiplicativeDecisionValid source components correspondences
        assignments ownerships false

structure P93CoupledRingChainAuthorityObservation
    (policy : P93CoupledRingChainAuthorityPolicy) where
  reviewedBaseName : P93RingChainBaseName
  baseNameCertificate : P93RingChainReviewedBaseNameCertificate
  annotatedBaseName : P93RingChainBaseName
  assignments : List (P93RingChainDescriptorAssignment policy.descriptorPolicies)
  multiplicativeSelected : Bool
  repeatedComponents : List P93RingChainRepeatedComponent
  componentCorrespondences : List P93RingChainComponentCorrespondence
  assignmentOwnerships : List P93RingChainAssignmentOwnership

def P93CoupledRingChainAuthorityObservation.ValidFor
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CoupledRingChainAuthorityObservation policy) : Prop :=
  observation.reviewedBaseName.Valid ∧
    observation.baseNameCertificate.ValidFor source observation.reviewedBaseName ∧
    policy.ReviewedBaseNameMatchesSource source observation.reviewedBaseName ∧
    observation.annotatedBaseName = observation.reviewedBaseName ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment =>
      assignment.unit.physicalIdentity).Nodup ∧
    (observation.assignments.filterMap fun assignment =>
      assignment.evidence.citation?).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      assignment.ValidFor policy source observation.reviewedBaseName) ∧
    (∀ unit,
      policy.StereogenicUnitEligible source observation.reviewedBaseName unit →
        ∃ assignment ∈ observation.assignments, assignment.unit = unit) ∧
    (observation.multiplicativeSelected = true ↔
      policy.MultiplicativeNameSelected source observation.reviewedBaseName) ∧
    policy.RepeatedComponentsObserved source observation.reviewedBaseName
      observation.repeatedComponents ∧
    P93RingChainMultiplicativeDecisionValid source observation.repeatedComponents
      observation.componentCorrespondences observation.assignments
      observation.assignmentOwnerships observation.multiplicativeSelected

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93RingChainComponentCorrespondence.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93RingChainReviewedBaseNameCertificate.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93RingChainReviewedBaseNameCertificate.constitution_eq_of_validFor
assert_kernel_only TetraStereo.OneCenter.P93RingChainMultiplicativeRejectionEvidence
assert_kernel_only TetraStereo.OneCenter.P93RingChainMultiplicativeSymmetryComplete
assert_kernel_only TetraStereo.OneCenter.P93RingChainMultiplicativeDecisionValid
assert_kernel_only TetraStereo.OneCenter.P93CoupledRingChainAuthorityObservation.ValidFor
