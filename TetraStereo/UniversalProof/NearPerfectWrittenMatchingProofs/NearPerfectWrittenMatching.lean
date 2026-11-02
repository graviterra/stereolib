import TetraStereo.OneCenter.ProductionCIPRule1aGeneralSoundness
import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedGlobal
import TetraStereo.OneCenter.ProductionCIPRule1aUniformFallbackSoundness
import TetraStereo.OneCenter.CIPAuthoritativeMancudeTotality

set_option autoImplicit false

/-!
# Near-perfect written mancude matchings

This module derives maximum cardinality for the written noncumulative double-bond matching from
an explicit structural sufficient condition: the localized component has at most
`2 * written.length + 1` vertices. Every competing matching saturates twice its edge count;
component cardinality bounds that saturation, and parity proves maximality.

The public saturation/component bounds do not require uniform atomic numbers or an already
successful label. Well-formedness and unique bond records remain explicit on the raw component
realization. Existing production maximum-matching totality theorems then give actual general
labeler and dispatcher success. Existing certified soundness supplies equality with the independent
maximum-matching average on semantically localized attachments. Molecule-wide near-perfect
components also derive the authoritative ranking's mancude support field.

Near-perfect coverage is sufficient, not necessary or universal. Components with larger deficiency
may have a maximum written matching; this construction does not decide those cases or establish
chemical admission/source fidelity. The general labeler's support condition is separate from the
dispatcher's shortcut and nonlocalized branches.

Closed even, odd and heterogeneous graph fixtures check this construction. The one-nitrogen
six-cycle has a literal general label `13/2`. Its chorded successor refuses the simple-cycle
shortcut and returns `19/3` through the general labeler and dispatcher. These are represented
finite graph regressions, not independently reviewed chemical source cases.
-/

namespace TetraStereo
namespace OneCenter

open DeclarativeCIP
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPCursorSupport

namespace MoleculeGraph

universe u

/-- The finite set of atoms in the localized mancude component of `attached`.  This is the public
replica of the file-private `mancudeComponentFinset` used by the uniform-fallback soundness proof,
stated for an arbitrary finite molecule graph. -/
noncomputable def mancudeComponentAtoms {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (attached : Atom) : Finset Atom := by
  classical
  exact Finset.univ.filter (molecule.InMancudeComponent attached)

/-- General cardinality bound, matching side: a matching only ever saturates atoms of the component
of `attached`.  This is the public replica of the file-private `saturationFinset_subset_component`;
it uses only the outside-component clause of `IsMancudeMatching`, so it needs no molecular or
well-formedness hypothesis. -/
theorem saturation_subset_mancudeComponentAtoms {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (attached : Atom)
    (partner : Atom → Option Atom)
    (hmatching : molecule.IsMancudeMatching attached partner) :
    (Finset.univ.filter fun atom => (partner atom).isSome) ⊆
      molecule.mancudeComponentAtoms attached := by
  classical
  intro atom hatom
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hatom
  simp only [mancudeComponentAtoms, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hnotComponent
  have hnone := hmatching.1 atom hnotComponent
  rw [hnone] at hatom
  simp at hatom

/-- General cardinality bound: the number of vertices a matching saturates never exceeds the
cardinality of the component it lives in. -/
theorem mancudeSaturation_le_mancudeComponentAtoms_card
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (attached : Atom)
    (partner : Atom → Option Atom)
    (hmatching : molecule.IsMancudeMatching attached partner) :
    mancudeSaturation partner ≤ (molecule.mancudeComponentAtoms attached).card := by
  classical
  simpa only [MoleculeGraph.mancudeSaturation] using
    Finset.card_le_card
      (molecule.saturation_subset_mancudeComponentAtoms attached partner hmatching)

end MoleculeGraph

namespace RawMolecule

/-- The written noncumulative double bonds inside the localized mancude component of `attached`.
This is exactly the filter consumed by `writtenMancudeEdges_isMatching` and by the production
`writtenDoubleCount` guard. -/
def writtenMancudeComponentEdges (mol : RawMolecule) (attached : ℕ) : List (ℕ × ℕ) :=
  (mol.localizedMancudeComponentEdges attached).filter fun edge =>
    mol.bondOrder edge.1 edge.2 == 2

/-- A finite structural sufficient-support check. False does not establish invalidity or
production refusal; larger-deficiency maximum matchings remain outside this sufficient check. -/
def nearPerfectMancudeComponent? (mol : RawMolecule) (attached : ℕ) : Bool :=
  decide ((mol.localizedMancudeComponentVertices attached).length ≤
    2 * (mol.writtenMancudeComponentEdges attached).length + 1)

@[simp] theorem nearPerfectMancudeComponent?_eq_true_iff (mol : RawMolecule) (attached : ℕ) :
    mol.nearPerfectMancudeComponent? attached = true ↔
      (mol.localizedMancudeComponentVertices attached).length ≤
        2 * (mol.writtenMancudeComponentEdges attached).length + 1 := by
  simp [nearPerfectMancudeComponent?]

/-- The exact finite component traversal bounds the declarative component cardinality.  The list is
not assumed duplicate-free: the bound goes through the injective image `Fin.val` and
`List.toFinset_card_le`, matching the fallback proof. -/
theorem mancudeComponentAtoms_card_le_localizedMancudeComponentVertices_length
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached : Fin mol.atomCount) :
    (mol.toMoleculeGraph.mancudeComponentAtoms attached).card ≤
      (mol.localizedMancudeComponentVertices attached.val).length := by
  classical
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let vertexFinset : Finset (Fin mol.atomCount) :=
    Finset.univ.filter fun atom => atom.val ∈ vertices
  have hcomponentInVertices :
      mol.toMoleculeGraph.mancudeComponentAtoms attached ⊆ vertexFinset := by
    intro atom hatom
    have hcomponent : mol.toMoleculeGraph.InMancudeComponent attached atom := by
      simpa [MoleculeGraph.mancudeComponentAtoms] using hatom
    simp only [vertexFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mol.mem_edgeComponent_localizedMancudeEdges_iff
      hwellFormed hunique attached atom).2 hcomponent
  have hvertexImageSubset : vertexFinset.image Fin.val ⊆ vertices.toFinset := by
    intro atom hatom
    simp only [Finset.mem_image] at hatom
    obtain ⟨source, hsource, rfl⟩ := hatom
    simp only [vertexFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hsource
    simpa using hsource
  have hvertexCardLe : vertexFinset.card ≤ vertices.length := by
    rw [← Finset.card_image_of_injective vertexFinset Fin.val_injective]
    exact (Finset.card_le_card hvertexImageSubset).trans (List.toFinset_card_le vertices)
  exact (Finset.card_le_card hcomponentInVertices).trans hvertexCardLe

/-- Public general cardinality bound on the raw side: every independent matching saturates at most
`localizedMancudeComponentVertices attached` many atoms. -/
theorem mancudeSaturation_le_localizedMancudeComponentVertices_length
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached : Fin mol.atomCount)
    (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hmatching : mol.toMoleculeGraph.IsMancudeMatching attached partner) :
    MoleculeGraph.mancudeSaturation partner ≤
      (mol.localizedMancudeComponentVertices attached.val).length :=
  (mol.toMoleculeGraph.mancudeSaturation_le_mancudeComponentAtoms_card attached partner
      hmatching).trans
    (mol.mancudeComponentAtoms_card_le_localizedMancudeComponentVertices_length
      hwellFormed hunique attached)

/-- **Written maximum from a near-perfect component.**  If the localized component of `attached` has
at most `2 * written.length + 1` vertices, the written noncumulative double bonds are a
maximum-cardinality matching of the whole localized component.  The proof compares an arbitrary
competitor matching (which saturates `2 * other.length` vertices, all inside the component, hence at
most `vertices.length`) with the near-perfect bound, and finishes by parity. -/
theorem writtenMancudeComponentEdges_isMaximum_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached : Fin mol.atomCount)
    (hnear : (mol.localizedMancudeComponentVertices attached.val).length ≤
      2 * (mol.writtenMancudeComponentEdges attached.val).length + 1) :
    IsMaximumMancudeEdgeMatching (mol.writtenMancudeComponentEdges attached.val)
      (mol.localizedMancudeComponentEdges attached.val) := by
  refine ⟨?_, ?_⟩
  · exact mol.writtenMancudeEdges_isMatching hwellFormed hunique attached
  · intro other hother
    have realization :=
      mol.localizedMancudeComponentEdges_realization hwellFormed hunique attached
    have hotherPartnerMatching : mol.toMoleculeGraph.IsMancudeMatching attached
        (partnerOfMancudeEdgeMatching (atomCount := mol.atomCount) other) :=
      partnerOfMancudeEdgeMatching_isMancudeMatching mol attached
        (mol.localizedMancudeComponentEdges attached.val) other realization hother
    have hotherBounds : ∀ edge ∈ other,
        edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount :=
      fun edge hedge => realization.endpointsInBounds edge (hother.1.subset hedge)
    have hotherLoop : ∀ edge ∈ other, edge.1 ≠ edge.2 :=
      fun edge hedge => realization.noSelfEdges edge (hother.1.subset hedge)
    have hotherSaturation :=
      mancudeSaturation_partnerOfMancudeEdgeMatching other hother.2 hotherBounds hotherLoop
    have hcardLe := mol.mancudeSaturation_le_localizedMancudeComponentVertices_length
      hwellFormed hunique attached
      (partnerOfMancudeEdgeMatching (atomCount := mol.atomCount) other) hotherPartnerMatching
    rw [hotherSaturation] at hcardLe
    omega

/-- The literal cheap check supplies an independently defined maximum-matching proof. -/
theorem writtenMancudeComponentEdges_isMaximum_of_nearPerfectCheck
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached : Fin mol.atomCount)
    (checked : mol.nearPerfectMancudeComponent? attached.val = true) :
    IsMaximumMancudeEdgeMatching (mol.writtenMancudeComponentEdges attached.val)
      (mol.localizedMancudeComponentEdges attached.val) :=
  mol.writtenMancudeComponentEdges_isMaximum_of_nearPerfect hwellFormed hunique attached
    ((mol.nearPerfectMancudeComponent?_eq_true_iff attached.val).mp checked)

/-- A sufficient molecule-level condition deriving maximum cardinality for each written matching.
This is not a necessary condition; larger-deficiency components may also have a maximum matching. -/
def NearPerfectMancudeComponents (mol : RawMolecule) : Prop :=
  ∀ attached : Fin mol.atomCount,
    (mol.localizedMancudeComponentVertices attached.val).length ≤
      2 * (mol.writtenMancudeComponentEdges attached.val).length + 1

/-- A near-perfect molecule satisfies the independent finite maximum-Kekulé condition used by the
authoritative totality module. -/
theorem localizedMancudeKekuleAdmissible_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hnear : mol.NearPerfectMancudeComponents) :
    LocalizedMancudeKekuleAdmissible mol := by
  intro attached
  exact mol.writtenMancudeComponentEdges_isMaximum_of_nearPerfect hwellFormed hunique attached
    (hnear attached)

/-- Actual general labeler totality specialized to the near-perfect hypothesis. -/
theorem generalMancudeRule1aLabel?_exists_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hnear : (mol.localizedMancudeComponentVertices attached.val).length ≤
      2 * (mol.writtenMancudeComponentEdges attached.val).length + 1) :
    ∃ label, mol.generalMancudeRule1aLabel? attached.val duplicated.val = some label :=
  mol.generalMancudeRule1aLabel?_exists_of_localized_maximum hwellFormed hunique attached duplicated
    hlocalized
    (mol.writtenMancudeComponentEdges_isMaximum_of_nearPerfect hwellFormed hunique attached hnear)

/-- Pointwise totality of the full production dispatcher `mancudeRule1aLabel?`.  The shortcut branch
is closed by its literal output; the remaining case is the near-perfect general branch. -/
theorem mancudeRule1aLabel?_exists_of_nearPerfect_pointwise
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hnear : (mol.localizedMancudeComponentVertices attached.val).length ≤
      2 * (mol.writtenMancudeComponentEdges attached.val).length + 1) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label :=
  mol.mancudeRule1aLabel?_exists_of_localized_maximum hwellFormed hunique attached duplicated
    hlocalized
    (mol.writtenMancudeComponentEdges_isMaximum_of_nearPerfect hwellFormed hunique attached hnear)

/-- **Actual dispatcher label totality.**  A molecule whose every localized component is
near-perfect produces a label for every attached--duplicate pair. -/
theorem mancudeRule1aLabel?_exists_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hnear : mol.NearPerfectMancudeComponents)
    (attached duplicated : ℕ) :
    ∃ label, mol.mancudeRule1aLabel? attached duplicated = some label := by
  by_cases hlocalized : containsUndirectedEdge mol.localizedMancudeEdges attached duplicated = true
  · rcases localizedMancudeEndpoints_lt mol hwellFormed attached duplicated hlocalized with
      ⟨attachedBound, duplicatedBound⟩
    exact mol.mancudeRule1aLabel?_exists_of_nearPerfect_pointwise hwellFormed hunique
      ⟨attached, attachedBound⟩ ⟨duplicated, duplicatedBound⟩ hlocalized
      (hnear ⟨attached, attachedBound⟩)
  · refine ⟨{ numerator := mol.atomZAt duplicated, denominator := 1 }, ?_⟩
    unfold RawMolecule.mancudeRule1aLabel?
    simp [Bool.eq_false_of_not_eq_true hlocalized]

/-- The production dispatcher is total on the near-perfect domain; a named proposition parallel to
the authoritative `MancudeRule1aSupported`. -/
def MancudeRule1aProductionSupported (mol : RawMolecule) : Prop :=
  ∀ attached duplicated, ∃ label, mol.mancudeRule1aLabel? attached duplicated = some label

/-- Molecule-wide production dispatcher totality from near-perfect components. -/
theorem mancudeRule1aProductionSupported_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hnear : mol.NearPerfectMancudeComponents) :
    mol.MancudeRule1aProductionSupported :=
  fun attached duplicated =>
    mol.mancudeRule1aLabel?_exists_of_nearPerfect hwellFormed hunique hnear attached duplicated

/-- **Totality and exactness without a successful-label premise.**  On a near-perfect component, a
semantically localized attached--duplicate pair admits a produced label whose exact rational value
is the independent maximum-matching average.  The opaque reference gate
`P92MancudeAttachmentRepresented` and the uniform-atomic-number shortcut are both replaced by the
structural near-perfect hypothesis; only the genuine localization premise is kept. -/
theorem mancudeRule1aLabel?_exact_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount)
    (hlocalized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
    (hnear : (mol.localizedMancudeComponentVertices attached.val).length ≤
      2 * (mol.writtenMancudeComponentEdges attached.val).length + 1) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label ∧
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  have hraw : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true :=
    (mol.containsUndirectedEdge_localizedMancudeEdges_iff
      hwellFormed hunique attached duplicated).2 hlocalized
  obtain ⟨label, hlabel⟩ :=
    mol.mancudeRule1aLabel?_exists_of_nearPerfect_pointwise hwellFormed hunique attached
      duplicated hraw hnear
  refine ⟨label, hlabel, ?_⟩
  have hsound :=
    mol.certifiedMancudeRule1aSound hwellFormed hunique attached duplicated label hlabel
  rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized hlocalized] at hsound
  exact hsound

/-- Molecule-wide support for the current authoritative ranking: on the near-perfect domain the
authoritative mancude dispatcher is total, so `DescriptorRule6HierarchySupport`'s
`mancude_rule1a_supported` field is derived rather than assumed. -/
theorem mancudeRule1aSupported_of_nearPerfect
    (mol : RawMolecule) (hwellFormed : mol.WellFormed) (hunique : mol.BondRecordsUnique)
    (hnear : mol.NearPerfectMancudeComponents) :
    MancudeRule1aSupported mol :=
  mancudeRule1aSupported_of_localizedKekuleAdmissible mol hwellFormed hunique
    (mol.localizedMancudeKekuleAdmissible_of_nearPerfect hwellFormed hunique hnear)

end RawMolecule

/-! ## Worked even / odd / heterogeneous examples -/

namespace NearPerfectExamples

open RawMolecule

/-- Even alternating six-membered carbocycle: the three written double bonds are a perfect matching
of the six-vertex component (`deficiency = 0`). -/
def evenRing : RawMolecule where
  atoms := List.replicate 6 (AtomSpec.aliphatic Element.C)
  bonds :=
    [⟨0, 1, ParsedBondKind.double⟩, ⟨1, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.double⟩, ⟨3, 4, ParsedBondKind.single⟩,
      ⟨4, 5, ParsedBondKind.double⟩, ⟨5, 0, ParsedBondKind.single⟩]

/-- Odd five-membered carbocycle with a formally negative unmatched position: two written double
bonds cover four of five vertices (`deficiency = 1`). -/
def oddRing : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
      { element := Element.C, charge := -1 }]
  bonds :=
    [⟨0, 1, ParsedBondKind.double⟩, ⟨1, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.double⟩, ⟨3, 4, ParsedBondKind.single⟩,
      ⟨4, 0, ParsedBondKind.single⟩]

/-- A represented six-membered ring with one nitrogen: atom zero can be matched to nitrogen
or carbon, testing a nonintegral average without a uniform-atomic-number premise. This graph
fixture is not independently approved chemical/source evidence. -/
def heterogeneousRing : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.N,
      AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C]
  bonds :=
    [⟨0, 1, ParsedBondKind.double⟩, ⟨1, 2, ParsedBondKind.single⟩,
      ⟨2, 3, ParsedBondKind.double⟩, ⟨3, 4, ParsedBondKind.single⟩,
      ⟨4, 5, ParsedBondKind.double⟩, ⟨5, 0, ParsedBondKind.single⟩]

theorem evenRing_wellFormed : evenRing.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK, RawMolecule.atomCount, evenRing]

theorem evenRing_bondRecordsUnique : evenRing.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, evenRing]

theorem oddRing_wellFormed : oddRing.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK, RawMolecule.atomCount, oddRing]

theorem oddRing_bondRecordsUnique : oddRing.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, oddRing]

theorem heterogeneousRing_wellFormed : heterogeneousRing.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK, RawMolecule.atomCount,
    heterogeneousRing]

theorem heterogeneousRing_bondRecordsUnique : heterogeneousRing.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, heterogeneousRing]

def evenRingAttached : Fin evenRing.atomCount := ⟨0, by decide⟩
def evenRingDuplicated : Fin evenRing.atomCount := ⟨1, by decide⟩

def oddRingAttached : Fin oddRing.atomCount := ⟨0, by decide⟩
def oddRingDuplicated : Fin oddRing.atomCount := ⟨1, by decide⟩

def heterogeneousRingAttached : Fin heterogeneousRing.atomCount := ⟨0, by decide⟩
def heterogeneousRingDuplicated : Fin heterogeneousRing.atomCount := ⟨1, by decide⟩

theorem evenRing_near :
    (evenRing.localizedMancudeComponentVertices evenRingAttached.val).length ≤
      2 * (evenRing.writtenMancudeComponentEdges evenRingAttached.val).length + 1 := by
  decide

theorem oddRing_near :
    (oddRing.localizedMancudeComponentVertices oddRingAttached.val).length ≤
      2 * (oddRing.writtenMancudeComponentEdges oddRingAttached.val).length + 1 := by
  decide

theorem heterogeneousRing_near :
    (heterogeneousRing.localizedMancudeComponentVertices heterogeneousRingAttached.val).length ≤
      2 * (heterogeneousRing.writtenMancudeComponentEdges heterogeneousRingAttached.val).length + 1 := by
  decide

theorem evenRing_writtenMaximum :
    IsMaximumMancudeEdgeMatching
      (evenRing.writtenMancudeComponentEdges evenRingAttached.val)
      (evenRing.localizedMancudeComponentEdges evenRingAttached.val) :=
  evenRing.writtenMancudeComponentEdges_isMaximum_of_nearPerfect
    evenRing_wellFormed evenRing_bondRecordsUnique evenRingAttached evenRing_near

theorem oddRing_writtenMaximum :
    IsMaximumMancudeEdgeMatching
      (oddRing.writtenMancudeComponentEdges oddRingAttached.val)
      (oddRing.localizedMancudeComponentEdges oddRingAttached.val) :=
  oddRing.writtenMancudeComponentEdges_isMaximum_of_nearPerfect
    oddRing_wellFormed oddRing_bondRecordsUnique oddRingAttached oddRing_near

theorem heterogeneousRing_writtenMaximum :
    IsMaximumMancudeEdgeMatching
      (heterogeneousRing.writtenMancudeComponentEdges heterogeneousRingAttached.val)
      (heterogeneousRing.localizedMancudeComponentEdges heterogeneousRingAttached.val) :=
  heterogeneousRing.writtenMancudeComponentEdges_isMaximum_of_nearPerfect
    heterogeneousRing_wellFormed heterogeneousRing_bondRecordsUnique heterogeneousRingAttached
    heterogeneousRing_near

/-- Even-ring totality and exactness: the produced label equals the independent average. -/
theorem evenRing_exact :
    ∃ label, evenRing.mancudeRule1aLabel? 0 1 = some label ∧
      label.toExactAtomicNumber.value =
        (evenRing.toMoleculeGraph.exactMancudeAverage evenRingAttached).value := by
  have hlocalized : evenRing.toMoleculeGraph.LocalizedMancudeEdge
      evenRingAttached evenRingDuplicated :=
    (evenRing.containsUndirectedEdge_localizedMancudeEdges_iff
      evenRing_wellFormed evenRing_bondRecordsUnique evenRingAttached evenRingDuplicated).1
      (by decide)
  exact evenRing.mancudeRule1aLabel?_exact_of_nearPerfect
    evenRing_wellFormed evenRing_bondRecordsUnique evenRingAttached evenRingDuplicated
    hlocalized evenRing_near

/-- Odd-ring totality and exactness: the unmatched electron-pair position is handled by the average
over the finite maximum-matching family. -/
theorem oddRing_exact :
    ∃ label, oddRing.mancudeRule1aLabel? 0 1 = some label ∧
      label.toExactAtomicNumber.value =
        (oddRing.toMoleculeGraph.exactMancudeAverage oddRingAttached).value := by
  have hlocalized : oddRing.toMoleculeGraph.LocalizedMancudeEdge
      oddRingAttached oddRingDuplicated :=
    (oddRing.containsUndirectedEdge_localizedMancudeEdges_iff
      oddRing_wellFormed oddRing_bondRecordsUnique oddRingAttached oddRingDuplicated).1
      (by decide)
  exact oddRing.mancudeRule1aLabel?_exact_of_nearPerfect
    oddRing_wellFormed oddRing_bondRecordsUnique oddRingAttached oddRingDuplicated
    hlocalized oddRing_near

/-- Heterogeneous-ring totality and exactness, with no uniform-atomic-number premise. -/
theorem heterogeneousRing_exact :
    ∃ label, heterogeneousRing.mancudeRule1aLabel? 0 1 = some label ∧
      label.toExactAtomicNumber.value =
        (heterogeneousRing.toMoleculeGraph.exactMancudeAverage
          heterogeneousRingAttached).value := by
  have hlocalized : heterogeneousRing.toMoleculeGraph.LocalizedMancudeEdge
      heterogeneousRingAttached heterogeneousRingDuplicated :=
    (heterogeneousRing.containsUndirectedEdge_localizedMancudeEdges_iff
      heterogeneousRing_wellFormed heterogeneousRing_bondRecordsUnique
      heterogeneousRingAttached heterogeneousRingDuplicated).1
      (by decide)
  exact heterogeneousRing.mancudeRule1aLabel?_exact_of_nearPerfect
    heterogeneousRing_wellFormed heterogeneousRing_bondRecordsUnique
    heterogeneousRingAttached heterogeneousRingDuplicated hlocalized heterogeneousRing_near

/-- The general labeler is called literally, even though this cycle also has a shortcut. -/
theorem evenRing_general_numeric :
    evenRing.generalMancudeRule1aLabel? 0 1 =
      some ({ numerator := 12, denominator := 2 } : CIPAtomicLabel) := by decide

theorem heterogeneousRing_general_numeric :
    heterogeneousRing.generalMancudeRule1aLabel? 0 1 =
      some ({ numerator := 13, denominator := 2 } : CIPAtomicLabel) := by decide

/-- A chorded represented graph exercises the general fallback. This is a graph fixture, not an
independently reviewed chemical source case. The root has three distinct possible matching partners. -/
def fallbackGraph : RawMolecule :=
  { heterogeneousRing with
    bonds := heterogeneousRing.bonds ++ [⟨0, 3, ParsedBondKind.single⟩] }

def fallbackAttached : Fin fallbackGraph.atomCount := ⟨0, by decide⟩
def fallbackDuplicated : Fin fallbackGraph.atomCount := ⟨1, by decide⟩

theorem fallbackGraph_wellFormed : fallbackGraph.WellFormed := by
  simp [RawMolecule.WellFormed, RawMolecule.BondEndpointsOK, RawMolecule.atomCount,
    fallbackGraph, heterogeneousRing]

theorem fallbackGraph_bondRecordsUnique : fallbackGraph.BondRecordsUnique := by
  simp [RawMolecule.BondRecordsUnique, RawBond.edgeKey, fallbackGraph, heterogeneousRing]

theorem fallbackGraph_near :
    (fallbackGraph.localizedMancudeComponentVertices 0).length ≤
      2 * (fallbackGraph.writtenMancudeComponentEdges 0).length + 1 := by decide

theorem fallbackGraph_no_shortcut : fallbackGraph.simpleMancudeCycle? 0 1 = none := by decide

theorem fallbackGraph_general_numeric :
    fallbackGraph.generalMancudeRule1aLabel? 0 1 =
      some ({ numerator := 19, denominator := 3 } : CIPAtomicLabel) := by decide

theorem fallbackGraph_dispatcher_numeric :
    fallbackGraph.mancudeRule1aLabel? 0 1 =
      some ({ numerator := 19, denominator := 3 } : CIPAtomicLabel) := by decide

/-- The structural sufficient condition feeds the existing independent exactness theorem. -/
theorem fallbackGraph_exact :
    ∃ label, fallbackGraph.mancudeRule1aLabel? 0 1 = some label ∧
      label.toExactAtomicNumber.value =
        (fallbackGraph.toMoleculeGraph.exactMancudeAverage fallbackAttached).value := by
  have hlocalized : fallbackGraph.toMoleculeGraph.LocalizedMancudeEdge
      fallbackAttached fallbackDuplicated :=
    (fallbackGraph.containsUndirectedEdge_localizedMancudeEdges_iff
      fallbackGraph_wellFormed fallbackGraph_bondRecordsUnique
      fallbackAttached fallbackDuplicated).mp (by decide)
  exact fallbackGraph.mancudeRule1aLabel?_exact_of_nearPerfect
    fallbackGraph_wellFormed fallbackGraph_bondRecordsUnique
    fallbackAttached fallbackDuplicated hlocalized fallbackGraph_near

end NearPerfectExamples

end OneCenter
end TetraStereo
