import TetraStereo.OneCenter.P93MolecularFullereneConfiguration

set_option autoImplicit false

/-!
# Graph-backed multiport fullerene addends

This module records the constitutional object attached to a fullerene cage without assuming that
one addend has only one cage attachment.  A port is an ordered pair whose first coordinate is a
cage atom and whose second coordinate is an atom of the external addend.  The validity judgment
is exact: the port set is precisely the positive cage-to-addend bond boundary, and the external
atom set is a connected, closed component after that boundary is removed.

`MolecularFullereneAddendRelationalEvidence` is deliberately a temporary name.  It is independent
of the older site-color evidence and can therefore be reviewed before any compatibility bridge or
replacement is made.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-- A complete external molecular graph together with all of its cage attachment ports.
The first coordinate of each port is a cage site; the second is an external atom. -/
structure MolecularFullereneAddend where
  externalAtoms : Finset Nat
  attachmentPorts : Finset (Nat × Nat)
  identityClass : Nat
  deriving DecidableEq

namespace MolecularFullereneAddend

/-- All cage sites touched by the addend.  A bridged addend may have more than one site. -/
def attachmentSites (addend : MolecularFullereneAddend) : Finset Nat :=
  addend.attachmentPorts.image Prod.fst

/-- The port set is exactly the positive molecular-bond boundary from the cage to this addend. -/
def PortJudgment (molecule : RawMolecule) (carrier : Finset Nat)
    (addend : MolecularFullereneAddend) : Prop :=
  (∀ site externalAtom,
      (site, externalAtom) ∈ addend.attachmentPorts ↔
        site ∈ carrier ∧ externalAtom ∈ addend.externalAtoms ∧
          0 < molecule.bondOrder site externalAtom) ∧
    ∀ site firstEndpoint secondEndpoint,
      (site, firstEndpoint) ∈ addend.attachmentPorts →
        (site, secondEndpoint) ∈ addend.attachmentPorts →
          firstEndpoint = secondEndpoint

/-- The declared external atoms form one nonempty, in-bounds, connected graph component.  Its
only positive bonds to atoms outside the component are exactly the declared cage ports. -/
def ExternalPartitionJudgment (molecule : RawMolecule) (carrier : Finset Nat)
    (addend : MolecularFullereneAddend) : Prop :=
  addend.externalAtoms.Nonempty ∧
    (∀ atom ∈ addend.externalAtoms, atom < molecule.atomCount ∧ atom ∉ carrier) ∧
    (∀ first ∈ addend.externalAtoms, ∀ second ∈ addend.externalAtoms,
      ∃ path, MolecularFullereneCagePath molecule addend.externalAtoms first second path) ∧
    ∀ atom ∈ addend.externalAtoms, ∀ neighbor,
      0 < molecule.bondOrder atom neighbor →
        neighbor ∈ addend.externalAtoms ∨ (neighbor, atom) ∈ addend.attachmentPorts

/-- Exact molecule-backed validity for a constitutional addend.  Positive identity classes are
reserved for actual addends; class zero remains available for an unsubstituted cage site. -/
def ValidFor (molecule : RawMolecule) (carrier : Finset Nat)
    (addend : MolecularFullereneAddend) : Prop :=
  0 < addend.identityClass ∧
    addend.attachmentPorts.Nonempty ∧
    addend.PortJudgment molecule carrier ∧
    addend.ExternalPartitionJudgment molecule carrier

theorem attachmentSites_mem_iff (addend : MolecularFullereneAddend) (site : Nat) :
    site ∈ addend.attachmentSites ↔
      ∃ externalAtom, (site, externalAtom) ∈ addend.attachmentPorts := by
  simp [attachmentSites]

theorem port_site_mem_attachmentSites {addend : MolecularFullereneAddend}
    {site externalAtom : Nat} (port : (site, externalAtom) ∈ addend.attachmentPorts) :
    site ∈ addend.attachmentSites := by
  exact attachmentSites_mem_iff addend site |>.2 ⟨externalAtom, port⟩

theorem validFor_port_exact {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : MolecularFullereneAddend} (valid : addend.ValidFor molecule carrier)
    (site externalAtom : Nat) :
    (site, externalAtom) ∈ addend.attachmentPorts ↔
      site ∈ carrier ∧ externalAtom ∈ addend.externalAtoms ∧
        0 < molecule.bondOrder site externalAtom :=
  valid.2.2.1.1 site externalAtom

theorem validFor_port_endpoint_unique {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : MolecularFullereneAddend} (valid : addend.ValidFor molecule carrier)
    (site firstEndpoint secondEndpoint : Nat)
    (firstPort : (site, firstEndpoint) ∈ addend.attachmentPorts)
    (secondPort : (site, secondEndpoint) ∈ addend.attachmentPorts) :
    firstEndpoint = secondEndpoint :=
  valid.2.2.1.2 site firstEndpoint secondEndpoint firstPort secondPort

theorem validFor_attachmentSites_subset {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : MolecularFullereneAddend} (valid : addend.ValidFor molecule carrier) :
    addend.attachmentSites ⊆ carrier := by
  intro site siteMem
  obtain ⟨externalAtom, port⟩ := attachmentSites_mem_iff addend site |>.1 siteMem
  exact (validFor_port_exact valid site externalAtom).1 port |>.1

theorem validFor_externalAtoms_disjoint {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : MolecularFullereneAddend} (valid : addend.ValidFor molecule carrier) :
    Disjoint addend.externalAtoms carrier := by
  rw [Finset.disjoint_left]
  intro atom external cage
  exact (valid.2.2.2.2.1 atom external).2 cage

theorem validFor_port_externalEndpoint {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : MolecularFullereneAddend} (valid : addend.ValidFor molecule carrier)
    {port : Nat × Nat} (portMem : port ∈ addend.attachmentPorts) :
    port.2 ∈ addend.externalAtoms := by
  exact ((validFor_port_exact valid port.1 port.2).1 portMem).2.1

/-- Multiport rooted constitutional isomorphism.  The external atom equivalence preserves atom
labels and all internal bond orders.  The attachment-site and port equivalences preserve the
incidence of each port with both its abstract site and its mapped external endpoint, as well as
the attachment bond order.  Cage locant numbers and relative cage placement are intentionally not
part of addend identity: the site equivalence makes a multiport addend an abstract hyperedge, whose
placement on the numbered cage remains a later cage-symmetry-stage judgment. -/
def ConstitutionallyIsomorphic (molecule : RawMolecule)
    (first second : MolecularFullereneAddend) : Prop :=
  ∃ atomEquivalence :
      { atom // atom ∈ first.externalAtoms } ≃ { atom // atom ∈ second.externalAtoms },
    (∀ atom,
      molecule.atomAt? atom.1 = molecule.atomAt? (atomEquivalence atom).1) ∧
    (∀ left right,
      molecule.bondOrder left.1 right.1 =
        molecule.bondOrder (atomEquivalence left).1 (atomEquivalence right).1) ∧
    ∃ siteEquivalence :
        { site // site ∈ first.attachmentSites } ≃
          { site // site ∈ second.attachmentSites },
      ∃ portEquivalence :
          { port // port ∈ first.attachmentPorts } ≃
            { port // port ∈ second.attachmentPorts },
        (∀ port,
          siteEquivalence
              ⟨port.1.1, port_site_mem_attachmentSites port.2⟩ =
            ⟨(portEquivalence port).1.1,
              port_site_mem_attachmentSites (portEquivalence port).2⟩) ∧
        (∀ port,
          ∃ firstEndpoint : port.1.2 ∈ first.externalAtoms,
            ∃ secondEndpoint : (portEquivalence port).1.2 ∈ second.externalAtoms,
              atomEquivalence ⟨port.1.2, firstEndpoint⟩ =
                ⟨(portEquivalence port).1.2, secondEndpoint⟩) ∧
        ∀ port,
          molecule.bondOrder port.1.1 port.1.2 =
            molecule.bondOrder (portEquivalence port).1.1 (portEquivalence port).1.2

theorem constitutionallyIsomorphic_refl (molecule : RawMolecule)
    (addend : MolecularFullereneAddend)
    (portsExternal : ∀ port ∈ addend.attachmentPorts,
      port.2 ∈ addend.externalAtoms) :
    addend.ConstitutionallyIsomorphic molecule addend := by
  refine ⟨Equiv.refl _, ?_, ?_, Equiv.refl _, Equiv.refl _, ?_, ?_, ?_⟩
  · intro atom
    rfl
  · intro left right
    rfl
  · intro port
    rfl
  · intro port
    have endpoint := portsExternal port.1 port.2
    exact ⟨endpoint, endpoint, rfl⟩
  · intro port
    rfl

theorem constitutionallyIsomorphic_refl_of_valid
    {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : MolecularFullereneAddend} (valid : addend.ValidFor molecule carrier) :
    addend.ConstitutionallyIsomorphic molecule addend :=
  constitutionallyIsomorphic_refl molecule addend fun _ portMem =>
    validFor_port_externalEndpoint valid portMem

/-! ## Unary specialization -/

/-- The ordinary one-site addend is the singleton-port specialization of the multiport model. -/
structure Unary where
  toAddend : MolecularFullereneAddend
  attachmentSite : Nat
  externalEndpoint : Nat
  attachmentPortsExact :
    toAddend.attachmentPorts = {(attachmentSite, externalEndpoint)}
  deriving DecidableEq

namespace Unary

def externalAtoms (addend : Unary) : Finset Nat := addend.toAddend.externalAtoms

def identityClass (addend : Unary) : Nat := addend.toAddend.identityClass

def attachmentPort (addend : Unary) : Nat × Nat :=
  (addend.attachmentSite, addend.externalEndpoint)

def ValidFor (molecule : RawMolecule) (carrier : Finset Nat) (addend : Unary) : Prop :=
  addend.toAddend.ValidFor molecule carrier

@[simp] theorem attachmentPorts (addend : Unary) :
    addend.toAddend.attachmentPorts = {addend.attachmentPort} := by
  exact addend.attachmentPortsExact

@[simp] theorem attachmentSites (addend : Unary) :
    addend.toAddend.attachmentSites = {addend.attachmentSite} := by
  unfold MolecularFullereneAddend.attachmentSites
  rw [addend.attachmentPortsExact]
  simp

theorem validFor_attachmentSite_mem {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : Unary} (valid : addend.ValidFor molecule carrier) :
    addend.attachmentSite ∈ carrier := by
  exact validFor_attachmentSites_subset valid (by simp)

theorem validFor_externalEndpoint_mem {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : Unary} (valid : addend.ValidFor molecule carrier) :
    addend.externalEndpoint ∈ addend.externalAtoms := by
  change addend.externalEndpoint ∈ addend.toAddend.externalAtoms
  exact ((validFor_port_exact valid addend.attachmentSite addend.externalEndpoint).1
    (by simp [attachmentPort])).2.1

theorem validFor_attachmentBond {molecule : RawMolecule} {carrier : Finset Nat}
    {addend : Unary} (valid : addend.ValidFor molecule carrier) :
    0 < molecule.bondOrder addend.attachmentSite addend.externalEndpoint := by
  exact (validFor_port_exact valid addend.attachmentSite addend.externalEndpoint).1
    (by simp [attachmentPort]) |>.2.2

end Unary

end MolecularFullereneAddend

/-! ## Complete relational evidence -/

/-- Exact partition of every in-bounds non-cage atom among the supplied addends. -/
def MolecularFullereneAddendExternalAtomsPartition
    (molecule : RawMolecule) (carrier : Finset Nat)
    (addends : List MolecularFullereneAddend) : Prop :=
  ∀ atom, atom < molecule.atomCount →
    (atom ∉ carrier ↔
      ∃ addend ∈ addends, atom ∈ addend.externalAtoms)

/-- Exact partition of the positive cage/external bond boundary among the supplied addends. -/
def MolecularFullereneAddendPortsPartition
    (molecule : RawMolecule) (carrier : Finset Nat)
    (addends : List MolecularFullereneAddend) : Prop :=
  ∀ site externalAtom,
    site ∈ carrier → externalAtom < molecule.atomCount → externalAtom ∉ carrier →
      (0 < molecule.bondOrder site externalAtom ↔
        ∃ addend ∈ addends, (site, externalAtom) ∈ addend.attachmentPorts)

/-- Graph-backed relational replacement for site colors.  It owns complete addend components,
requires exact atom and port partitions, and makes equality of positive identity classes
equivalent to multiport constitutional isomorphism.  It intentionally does not reuse the older
`MolecularFullereneSubstitutionEvidence` name. -/
structure MolecularFullereneAddendRelationalEvidence
    (molecule : RawMolecule) (carrier : Finset Nat) where
  addends : List MolecularFullereneAddend
  originalDerivativeChiral : Bool
  chiralAddends : Finset MolecularFullereneAddend
  addendsNonempty : addends ≠ []
  addendsNodup : addends.Nodup
  addendsValid : ∀ addend ∈ addends, addend.ValidFor molecule carrier
  externalAtomsPairwiseDisjoint :
    addends.Pairwise fun first second => Disjoint first.externalAtoms second.externalAtoms
  attachmentSitesPairwiseDisjoint :
    addends.Pairwise fun first second => Disjoint first.attachmentSites second.attachmentSites
  externalAtomsPartition :
    MolecularFullereneAddendExternalAtomsPartition molecule carrier addends
  attachmentPortsPartition :
    MolecularFullereneAddendPortsPartition molecule carrier addends
  identityClassesFaithful : ∀ first ∈ addends, ∀ second ∈ addends,
    first.identityClass = second.identityClass ↔
      first.ConstitutionallyIsomorphic molecule second
  chiralAddendsOwned : ∀ addend ∈ chiralAddends, addend ∈ addends
  chiralIdentityFaithful : ∀ first ∈ addends, ∀ second ∈ addends,
    first.identityClass = second.identityClass →
      (first ∈ chiralAddends ↔ second ∈ chiralAddends)

namespace MolecularFullereneAddendRelationalEvidence

/-- Reporting projection of a multiport evidence family to its occupied cage sites.  For a
multiport addend this deliberately forgets hyperedge grouping and therefore is not, by itself, a
cage-symmetry coloring semantics. -/
noncomputable def substitutedSites
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) : Finset Nat :=
  (evidence.addends.flatMap fun addend => addend.attachmentSites.toList).toFinset

/-- Reporting projection to sites attached to an intrinsically chiral addend.  Like
`substitutedSites`, this set is not a symmetry semantics for general multiport addends. -/
noncomputable def chiralSubstituentSites
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) : Finset Nat :=
  (evidence.chiralAddends.toList.flatMap fun addend => addend.attachmentSites.toList).toFinset

/-- Relational per-site identity projection.  Pairwise site disjointness makes this relation
single-valued without introducing a caller-authored site-indexed identity array. -/
def IdentityClassAt
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    (site identityClass : Nat) : Prop :=
  ∃ addend ∈ evidence.addends,
    site ∈ addend.attachmentSites ∧ addend.identityClass = identityClass

/-- The exact regime in which site-wise reporting loses no multiport grouping: every evidence
addend has a proof-carrying singleton-port specialization. -/
def UnaryOnly
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) : Prop :=
  ∀ addend ∈ evidence.addends,
    ∃ unary : MolecularFullereneAddend.Unary, unary.toAddend = addend

theorem mem_substitutedSites_iff
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) (site : Nat) :
    site ∈ evidence.substitutedSites ↔
      ∃ addend ∈ evidence.addends, site ∈ addend.attachmentSites := by
  simp [substitutedSites]

theorem substitutedSites_subset
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) :
    evidence.substitutedSites ⊆ carrier := by
  intro site siteMem
  obtain ⟨addend, addendMem, siteInAddend⟩ :=
    (evidence.mem_substitutedSites_iff site).1 siteMem
  exact MolecularFullereneAddend.validFor_attachmentSites_subset
    (evidence.addendsValid addend addendMem) siteInAddend

theorem chiralSubstituentSites_subset
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier) :
    evidence.chiralSubstituentSites ⊆ evidence.substitutedSites := by
  intro site siteMem
  simp only [chiralSubstituentSites, List.mem_toFinset, List.mem_flatMap,
    Finset.mem_toList] at siteMem
  obtain ⟨addend, addendChiral, siteInAddend⟩ := siteMem
  apply evidence.mem_substitutedSites_iff site |>.2
  exact ⟨addend, evidence.chiralAddendsOwned addend addendChiral, siteInAddend⟩

theorem identityClassAt_exists_of_mem_substitutedSites
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    {site : Nat} (siteMem : site ∈ evidence.substitutedSites) :
    ∃ identityClass, evidence.IdentityClassAt site identityClass := by
  obtain ⟨addend, addendMem, siteInAddend⟩ :=
    (evidence.mem_substitutedSites_iff site).1 siteMem
  exact ⟨addend.identityClass, addend, addendMem, siteInAddend, rfl⟩

theorem addend_eq_of_common_attachmentSite
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    {first second : MolecularFullereneAddend}
    (firstMem : first ∈ evidence.addends) (secondMem : second ∈ evidence.addends)
    {site : Nat} (firstSite : site ∈ first.attachmentSites)
    (secondSite : site ∈ second.attachmentSites) :
    first = second := by
  by_contra distinct
  have pairwiseOnSet :
      (evidence.addends.toFinset : Set MolecularFullereneAddend).Pairwise
        (fun left right => Disjoint left.attachmentSites right.attachmentSites) :=
    (List.pairwise_iff_coe_toFinset_pairwise evidence.addendsNodup
      (fun _ _ disjoint => disjoint.symm)).2 evidence.attachmentSitesPairwiseDisjoint
  have disjoint := pairwiseOnSet (by simpa using firstMem) (by simpa using secondMem) distinct
  exact (Finset.disjoint_left.mp disjoint) firstSite secondSite

theorem identityClassAt_unique
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    {site firstClass secondClass : Nat}
    (firstIdentity : evidence.IdentityClassAt site firstClass)
    (secondIdentity : evidence.IdentityClassAt site secondClass) :
    firstClass = secondClass := by
  obtain ⟨first, firstMem, firstSite, firstClassExact⟩ := firstIdentity
  obtain ⟨second, secondMem, secondSite, secondClassExact⟩ := secondIdentity
  have sameAddend := evidence.addend_eq_of_common_attachmentSite
    firstMem secondMem firstSite secondSite
  subst second
  exact firstClassExact.symm.trans secondClassExact

/-- In a unary-only family, the relational site projection is exactly equivalent to a unique
proof-carrying unary addend with that site and identity class. -/
theorem unaryOnly_identityClassAt_iff
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    (unaryOnly : evidence.UnaryOnly) (site identityClass : Nat) :
    evidence.IdentityClassAt site identityClass ↔
      ∃ unary : MolecularFullereneAddend.Unary,
        unary.toAddend ∈ evidence.addends ∧
          unary.attachmentSite = site ∧ unary.identityClass = identityClass := by
  constructor
  · rintro ⟨addend, addendMem, siteMem, classExact⟩
    obtain ⟨unary, rfl⟩ := unaryOnly addend addendMem
    have siteExact : unary.attachmentSite = site := by
      have reversed : site = unary.attachmentSite := by simpa using siteMem
      exact reversed.symm
    exact ⟨unary, addendMem, siteExact, classExact⟩
  · rintro ⟨unary, unaryMem, siteExact, classExact⟩
    refine ⟨unary.toAddend, unaryMem, ?_, classExact⟩
    rw [MolecularFullereneAddend.Unary.attachmentSites, siteExact]
    simp

/-- Unary site identities are faithful to the full graph relation: equal projected classes at two
sites are equivalent to constitutional isomorphism of their unique unary addends. -/
theorem unaryOnly_identityClasses_faithful
    {molecule : RawMolecule} {carrier : Finset Nat}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule carrier)
    (unaryOnly : evidence.UnaryOnly)
    {firstSite secondSite firstClass secondClass : Nat}
    (firstIdentity : evidence.IdentityClassAt firstSite firstClass)
    (secondIdentity : evidence.IdentityClassAt secondSite secondClass) :
    firstClass = secondClass ↔
      ∃ firstUnary secondUnary : MolecularFullereneAddend.Unary,
        firstUnary.toAddend ∈ evidence.addends ∧
          secondUnary.toAddend ∈ evidence.addends ∧
          firstUnary.attachmentSite = firstSite ∧
          secondUnary.attachmentSite = secondSite ∧
          firstUnary.identityClass = firstClass ∧
          secondUnary.identityClass = secondClass ∧
          firstUnary.toAddend.ConstitutionallyIsomorphic molecule secondUnary.toAddend := by
  obtain ⟨firstUnary, firstMem, firstSiteExact, firstClassExact⟩ :=
    (evidence.unaryOnly_identityClassAt_iff unaryOnly firstSite firstClass).1 firstIdentity
  obtain ⟨secondUnary, secondMem, secondSiteExact, secondClassExact⟩ :=
    (evidence.unaryOnly_identityClassAt_iff unaryOnly secondSite secondClass).1 secondIdentity
  constructor
  · intro classesEqual
    refine ⟨firstUnary, secondUnary, firstMem, secondMem, firstSiteExact, secondSiteExact,
      firstClassExact, secondClassExact, ?_⟩
    apply (evidence.identityClassesFaithful firstUnary.toAddend firstMem
      secondUnary.toAddend secondMem).1
    exact firstClassExact.trans (classesEqual.trans secondClassExact.symm)
  · rintro ⟨firstUnary', secondUnary', firstMem', secondMem', _firstSite', _secondSite',
      firstClass', secondClass', isomorphic⟩
    have classEquality := (evidence.identityClassesFaithful firstUnary'.toAddend firstMem'
      secondUnary'.toAddend secondMem').2 isomorphic
    exact firstClass'.symm.trans (classEquality.trans secondClass')

end MolecularFullereneAddendRelationalEvidence

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
