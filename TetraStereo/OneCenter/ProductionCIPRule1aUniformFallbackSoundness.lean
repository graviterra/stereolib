import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedGlobal

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace MoleculeGraph

universe u

private theorem localizedVertex_doubleNeighbor_unique
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (vertex first second : Atom)
    (hvertex : molecule.LocalizedMancudeVertex vertex)
    (hfirst : molecule.bond vertex first = 2)
    (hsecond : molecule.bond vertex second = 2) :
    first = second := by
  have hfirstMem : first ∈ (Finset.univ : Finset Atom).filter
      (fun other => molecule.bond vertex other = 2) := by
    simp [hfirst]
  have hsecondMem : second ∈ (Finset.univ : Finset Atom).filter
      (fun other => molecule.bond vertex other = 2) := by
    simp [hsecond]
  have hcount : molecule.incidentDoubleBondCount vertex = 1 := by
    rcases hvertex with hmatched | ⟨hunmatched, _⟩
    · exact hmatched
    · have hpositive : 0 < ((Finset.univ : Finset Atom).filter
          (fun other => molecule.bond vertex other = 2)).card :=
        Finset.card_pos.mpr ⟨first, hfirstMem⟩
      unfold incidentDoubleBondCount at hunmatched
      rw [hunmatched] at hpositive
      omega
  unfold incidentDoubleBondCount at hcount
  obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hcount
  rw [honly] at hfirstMem hsecondMem
  have hfirstEq : first = only := by simpa using hfirstMem
  have hsecondEq : second = only := by simpa using hsecondMem
  exact hfirstEq.trans hsecondEq.symm

end MoleculeGraph

namespace RawMolecule

/-- The written double bonds in a localized mancude component form an occurrence-level matching. -/
theorem writtenMancudeEdges_isMatching
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached : Fin mol.atomCount) :
    let edges := mol.localizedMancudeComponentEdges attached.val
    let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
    IsMancudeEdgeMatching written edges := by
  dsimp only
  let edges := mol.localizedMancudeComponentEdges attached.val
  let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
  let realization := mol.localizedMancudeComponentEdges_realization
    hwellFormed hunique attached
  refine ⟨List.filter_sublist, ?_⟩
  apply (realization.nodup.sublist List.filter_sublist).pairwise_of_forall_ne
  intro first hfirst second hsecond hne
  have hfirstParts := List.mem_filter.1 hfirst
  have hsecondParts := List.mem_filter.1 hsecond
  have hfirstBounds := realization.endpointsInBounds first hfirstParts.1
  have hsecondBounds := realization.endpointsInBounds second hsecondParts.1
  let firstLeft : Fin mol.atomCount := ⟨first.1, hfirstBounds.1⟩
  let firstRight : Fin mol.atomCount := ⟨first.2, hfirstBounds.2⟩
  let secondLeft : Fin mol.atomCount := ⟨second.1, hsecondBounds.1⟩
  let secondRight : Fin mol.atomCount := ⟨second.2, hsecondBounds.2⟩
  have hfirstMatched : NatEdgeMatchedBy edges firstLeft firstRight :=
    ⟨first, hfirstParts.1, Or.inl rfl⟩
  have hsecondMatched : NatEdgeMatchedBy edges secondLeft secondRight :=
    ⟨second, hsecondParts.1, Or.inl rfl⟩
  have hfirstLocalized := (realization.localizedComponent_iff firstLeft firstRight).1
    hfirstMatched |>.1
  have hsecondLocalized := (realization.localizedComponent_iff secondLeft secondRight).1
    hsecondMatched |>.1
  have hfirstDouble : mol.toMoleculeGraph.bond firstLeft firstRight = 2 := by
    change mol.bondOrder first.1 first.2 = 2
    simpa using hfirstParts.2
  have hsecondDouble : mol.toMoleculeGraph.bond secondLeft secondRight = 2 := by
    change mol.bondOrder second.1 second.2 = 2
    simpa using hsecondParts.2
  have hfirstLeftUnique (other : Fin mol.atomCount)
      (hother : mol.toMoleculeGraph.bond firstLeft other = 2) :
      other = firstRight :=
    mol.toMoleculeGraph.localizedVertex_doubleNeighbor_unique
      firstLeft other firstRight hfirstLocalized.1.2.1 hother hfirstDouble
  have hfirstRightUnique (other : Fin mol.atomCount)
      (hother : mol.toMoleculeGraph.bond firstRight other = 2) :
      other = firstLeft :=
    mol.toMoleculeGraph.localizedVertex_doubleNeighbor_unique
      firstRight other firstLeft hfirstLocalized.1.2.2 hother
        (by simpa [mol.toMoleculeGraph.bond_symm] using hfirstDouble)
  have hsecondDoubleSymm : mol.toMoleculeGraph.bond secondRight secondLeft = 2 := by
    simpa [mol.toMoleculeGraph.bond_symm] using hsecondDouble
  simp only [MancudeEdgesDisjoint, Bool.and_eq_true, bne_iff_ne]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro heq
    have hleft : secondLeft = firstLeft := Fin.ext heq
    have hright : secondRight = firstRight := by
      apply hfirstLeftUnique
      simpa [hleft] using hsecondDouble
    apply hne
    apply realization.undirectedUnique first hfirstParts.1 second hsecondParts.1
    left
    exact Prod.ext (congrArg Fin.val hleft).symm (congrArg Fin.val hright).symm
  · intro heq
    have hrightLeft : secondRight = firstLeft := Fin.ext heq
    have hleftRight : secondLeft = firstRight := by
      apply hfirstLeftUnique
      simpa [hrightLeft] using hsecondDoubleSymm
    apply hne
    apply realization.undirectedUnique first hfirstParts.1 second hsecondParts.1
    right
    exact Prod.ext (congrArg Fin.val hrightLeft).symm
      (congrArg Fin.val hleftRight).symm
  · intro heq
    have hleftRight : secondLeft = firstRight := Fin.ext heq
    have hrightLeft : secondRight = firstLeft := by
      apply hfirstRightUnique
      simpa [hleftRight] using hsecondDouble
    apply hne
    apply realization.undirectedUnique first hfirstParts.1 second hsecondParts.1
    right
    exact Prod.ext (congrArg Fin.val hrightLeft).symm
      (congrArg Fin.val hleftRight).symm
  · intro heq
    have hright : secondRight = firstRight := Fin.ext heq
    have hleft : secondLeft = firstLeft := by
      apply hfirstRightUnique
      simpa [hright] using hsecondDoubleSymm
    apply hne
    apply realization.undirectedUnique first hfirstParts.1 second hsecondParts.1
    left
    exact Prod.ext (congrArg Fin.val hleft).symm (congrArg Fin.val hright).symm

private noncomputable def mancudeComponentFinset (mol : RawMolecule)
    (attached : Fin mol.atomCount) : Finset (Fin mol.atomCount) := by
  classical
  exact Finset.univ.filter (mol.toMoleculeGraph.InMancudeComponent attached)

private theorem saturationFinset_subset_component
    (mol : RawMolecule) (attached : Fin mol.atomCount)
    (partner : Fin mol.atomCount → Option (Fin mol.atomCount))
    (hmatching : mol.toMoleculeGraph.IsMancudeMatching attached partner) :
    (Finset.univ.filter fun atom => (partner atom).isSome) ⊆
      mol.mancudeComponentFinset attached := by
  classical
  intro atom hatom
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hatom
  simp only [mancudeComponentFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hnotComponent
  have hnone := hmatching.1 atom hnotComponent
  rw [hnone] at hatom
  simp at hatom

/-- The large-component fallback is sound for every successful localized invocation.  The proof
uses the written double bonds as a perfect matching witness, then shows every independent maximum
matching saturates the whole realized component; uniform component atomic number therefore fixes
the attached contribution in every Kekule form. -/
theorem uniformPerfectMancudeRule1aLabel?_sound_of_raw_localized
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (label : CIPAtomicLabel)
    (hlabel : mol.uniformPerfectMancudeRule1aLabel?
      attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  classical
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let edges := mol.localizedMancudeComponentEdges attached.val
  let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
  let uniformAtomicNumber := vertices.all fun atom =>
    mol.atomZAt atom == mol.atomZAt attached.val
  unfold uniformPerfectMancudeRule1aLabel? at hlabel
  change (if !(vertices.contains duplicated.val) || edges.isEmpty ||
      vertices.length != 2 * written.length || !uniformAtomicNumber then none
    else some ⟨mol.atomZAt attached.val, 1⟩) = some label at hlabel
  split at hlabel <;> rename_i hguard
  · contradiction
  · have hlabelEq : label = ⟨mol.atomZAt attached.val, 1⟩ :=
      (Option.some.inj hlabel).symm
    subst label
    have hguardFalse : (!vertices.contains duplicated.val || edges.isEmpty ||
        vertices.length != 2 * written.length || !uniformAtomicNumber) = false :=
      Bool.eq_false_of_not_eq_true hguard
    have hguardRaw :
        (((!vertices.contains duplicated.val) = false ∧ edges.isEmpty = false) ∧
          (vertices.length != 2 * written.length) = false) ∧
            (!uniformAtomicNumber) = false := by
      simpa only [Bool.or_eq_false_iff] using hguardFalse
    have hguardParts : vertices.contains duplicated.val = true ∧
        edges.isEmpty = false ∧
        vertices.length = 2 * written.length ∧ uniformAtomicNumber = true := by
      refine ⟨?_, hguardRaw.1.1.2, ?_, ?_⟩
      · simpa using hguardRaw.1.1.1
      · simpa using hguardRaw.1.2
      · simpa using hguardRaw.2
    have hwritten : IsMancudeEdgeMatching written edges := by
      simpa [edges, written] using
        mol.writtenMancudeEdges_isMatching hwellFormed hunique attached
    let realization := mol.localizedMancudeComponentEdges_realization
      hwellFormed hunique attached
    let writtenPartner := partnerOfMancudeEdgeMatching
      (atomCount := mol.atomCount) written
    have hwrittenPartnerMatching :
        mol.toMoleculeGraph.IsMancudeMatching attached writtenPartner :=
      partnerOfMancudeEdgeMatching_isMancudeMatching
        mol attached edges written realization hwritten
    have hwrittenBounds : ∀ edge ∈ written,
        edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
      intro edge hedge
      exact realization.endpointsInBounds edge (hwritten.1.subset hedge)
    have hwrittenLoop : ∀ edge ∈ written, edge.1 ≠ edge.2 := by
      intro edge hedge
      exact realization.noSelfEdges edge (hwritten.1.subset hedge)
    have hwrittenSaturation : MoleculeGraph.mancudeSaturation writtenPartner =
        vertices.length := by
      rw [mancudeSaturation_partnerOfMancudeEdgeMatching written
        hwritten.2 hwrittenBounds hwrittenLoop]
      exact hguardParts.2.2.1.symm
    let vertexFinset : Finset (Fin mol.atomCount) :=
      Finset.univ.filter fun atom => atom.val ∈ vertices
    have hcomponentInVertices : mol.mancudeComponentFinset attached ⊆ vertexFinset := by
      intro atom hatom
      have hcomponent : mol.toMoleculeGraph.InMancudeComponent attached atom := by
        simpa [mancudeComponentFinset] using hatom
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
      exact (Finset.card_le_card hvertexImageSubset).trans
        (List.toFinset_card_le vertices)
    have hcomponentCardLe : (mol.mancudeComponentFinset attached).card ≤ vertices.length :=
      (Finset.card_le_card hcomponentInVertices).trans hvertexCardLe
    have hwrittenSubset := mol.saturationFinset_subset_component attached
      writtenPartner hwrittenPartnerMatching
    have hwrittenCard : (Finset.univ.filter fun atom =>
        (writtenPartner atom).isSome).card = vertices.length := hwrittenSaturation
    have hcomponentCard : (mol.mancudeComponentFinset attached).card = vertices.length := by
      have hle := Finset.card_le_card hwrittenSubset
      rw [hwrittenCard] at hle
      omega
    have hmaximumSaturates : ∀ partner ∈
        mol.toMoleculeGraph.maximumMancudeMatchings attached,
        MoleculeGraph.mancudeSaturation partner = vertices.length := by
      intro partner hpartner
      have hmaximum : mol.toMoleculeGraph.IsMaximumMancudeMatching attached partner :=
        (Finset.mem_filter.1 hpartner).2
      have hlower := hmaximum.2 writtenPartner hwrittenPartnerMatching
      rw [hwrittenSaturation] at hlower
      have hsubset := mol.saturationFinset_subset_component attached partner hmaximum.1
      have hupper := Finset.card_le_card hsubset
      change MoleculeGraph.mancudeSaturation partner ≤ _ at hupper
      rw [hcomponentCard] at hupper
      omega
    have hpartnerContribution : ∀ partner ∈
        mol.toMoleculeGraph.maximumMancudeMatchings attached,
        mol.toMoleculeGraph.mancudePartnerAtomicNumber attached partner =
          mol.atomZAt attached.val := by
      intro partner hpartner
      have hmaximum : mol.toMoleculeGraph.IsMaximumMancudeMatching attached partner :=
        (Finset.mem_filter.1 hpartner).2
      have hsubset := mol.saturationFinset_subset_component attached partner hmaximum.1
      have hsubsetCard := Finset.card_le_card hsubset
      have hsaturation := hmaximumSaturates partner hpartner
      change MoleculeGraph.mancudeSaturation partner ≤ _ at hsubsetCard
      rw [hsaturation, hcomponentCard] at hsubsetCard
      have hreverseCard : (mol.mancudeComponentFinset attached).card ≤
          (Finset.univ.filter fun atom => (partner atom).isSome).card := by
        change (mol.mancudeComponentFinset attached).card ≤
          MoleculeGraph.mancudeSaturation partner
        rw [hcomponentCard, hsaturation]
      have heq : (Finset.univ.filter fun atom => (partner atom).isSome) =
          mol.mancudeComponentFinset attached :=
        Finset.eq_of_subset_of_card_le hsubset hreverseCard
      have hattachedComponent : attached ∈ mol.mancudeComponentFinset attached := by
        simp only [mancudeComponentFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Relation.ReflTransGen.refl
      have hattachedSome : (partner attached).isSome := by
        have : attached ∈ (Finset.univ.filter fun atom => (partner atom).isSome) := by
          rw [heq]
          exact hattachedComponent
        simpa using this
      obtain ⟨other, hother⟩ := Option.isSome_iff_exists.1 hattachedSome
      have hlocalizedOther := ((hmaximum.1.2 attached other).1 hother).2
      have hotherComponent : mol.toMoleculeGraph.InMancudeComponent attached other :=
        Relation.ReflTransGen.refl.tail hlocalizedOther
      have hotherMem : other.val ∈ vertices :=
        (mol.mem_edgeComponent_localizedMancudeEdges_iff
          hwellFormed hunique attached other).2 hotherComponent
      have huniform : mol.atomZAt other.val = mol.atomZAt attached.val := by
        have hall := List.all_eq_true.mp hguardParts.2.2.2 other.val hotherMem
        simpa [uniformAtomicNumber] using hall
      unfold MoleculeGraph.mancudePartnerAtomicNumber
      simp only [hother]
      change mol.toMoleculeGraph.atomZ other = mol.atomZAt attached.val
      rw [← mol.atomZAt_eq_toMoleculeGraph_atomZ other.val other.2]
      exact huniform
    have hsum : (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
        (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) =
          (mol.toMoleculeGraph.maximumMancudeMatchings attached).card *
            mol.atomZAt attached.val := by
      rw [Finset.sum_congr rfl hpartnerContribution]
      simp
    have hsemantic : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated :=
      (mol.containsUndirectedEdge_localizedMancudeEdges_iff
        hwellFormed hunique attached duplicated).1 hlocalized
    rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized hsemantic]
    unfold CIPAtomicLabel.toExactAtomicNumber CIPAtomicLabel.effectiveDenominator
      ExactAtomicNumber.value MoleculeGraph.exactMancudeAverage
    rw [hsum]
    have hcountPositive : 0 <
        (mol.toMoleculeGraph.maximumMancudeMatchings attached).card :=
      Finset.card_pos.mpr (mol.toMoleculeGraph.maximumMancudeMatchings_nonempty attached)
    norm_num
    field_simp

/-- Every successful first-sphere label for a multiple-bond duplicate is exact.  The certified
uniform-perfect shortcut is attempted before the exhaustive general matcher. -/
theorem canonicalFirstSphereRule1aLabel?_multiple_sound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (node : CanonicalBranchNode)
    (distance : ℕ)
    (hprovenance : node.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance)
    (attached duplicated : Fin mol.atomCount)
    (hattached : attached.val = node.parent)
    (hduplicated : duplicated.val = node.atom)
    (label : CIPAtomicLabel)
    (hlabel : mol.canonicalFirstSphereRule1aLabel? node = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  unfold canonicalFirstSphereRule1aLabel? at hlabel
  simp only [hprovenance] at hlabel
  split at hlabel <;> rename_i localized
  · cases huniform : mol.uniformPerfectMancudeRule1aLabel?
        node.parent node.atom with
    | some uniformLabel =>
        simp only [huniform] at hlabel
        have hlabelEq : label = uniformLabel := (Option.some.inj hlabel).symm
        subst label
        apply mol.uniformPerfectMancudeRule1aLabel?_sound_of_raw_localized
          hwellFormed hunique attached duplicated
        · simpa [hattached, hduplicated] using localized
        · simpa [hattached, hduplicated] using huniform
    | none =>
        apply mol.certifiedMancudeRule1aSound hwellFormed hunique attached duplicated label
        have hmancude : mol.mancudeRule1aLabel? node.parent node.atom = some label := by
          simpa [canonicalRule1aLabel?, hprovenance, huniform] using hlabel
        simpa [hattached, hduplicated] using hmancude
  · apply mol.certifiedMancudeRule1aSound hwellFormed hunique attached duplicated label
    have hmancude : mol.mancudeRule1aLabel? node.parent node.atom = some label := by
      simpa [canonicalRule1aLabel?, hprovenance] using hlabel
    simpa [hattached, hduplicated] using hmancude

end RawMolecule

end
end OneCenter
end TetraStereo
