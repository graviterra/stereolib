import TetraStereo.OneCenter.ProductionCIPRule1aCycleEnumeration
import TetraStereo.OneCenter.ProductionCIPRule1aMatchingRealization

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-- The attached-atom contribution multiset obtained by explicitly enumerating every maximum raw
edge matching.  Unlike the final rational label, this retains the complete finite witness family. -/
def executableMaximumPartnerProfile (mol : RawMolecule) (attached : ℕ)
    (edges : List (ℕ × ℕ)) : Multiset ℕ :=
  (maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)).map
    (mol.mancudeEdgeMatchingPartnerZ attached)

/-- A mechanically checkable even-cycle certificate: exhaustive raw matching enumeration has
exactly the two required attached-partner contributions. -/
def EvenCycleMatchingCertificate (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ)) (first second : Fin mol.atomCount) : Prop :=
  mol.executableMaximumPartnerProfile attached.val edges =
    {mol.toMoleculeGraph.atomZ first, mol.toMoleculeGraph.atomZ second}

/-- A mechanically checkable odd-cycle certificate: exhaustive raw matching enumeration has `k`
copies of each neighbouring contribution and one unmatched contribution. -/
def OddCycleMatchingCertificate (mol : RawMolecule) (attached : Fin mol.atomCount)
    (edges : List (ℕ × ℕ)) (first second : Fin mol.atomCount) (k : ℕ) : Prop :=
  mol.executableMaximumPartnerProfile attached.val edges =
    Multiset.replicate k (mol.toMoleculeGraph.atomZ first) +
      Multiset.replicate k (mol.toMoleculeGraph.atomZ second) + {0}

/-- Stronger even certificate exposing the two actual maximum raw edge matchings.  Every field is
finite data or an equality over finite data and can be discharged by kernel computation. -/
def EvenCycleEdgeEnumerationCertificate (mol : RawMolecule)
    (attached : Fin mol.atomCount) (edges : List (ℕ × ℕ))
    (first second : Fin mol.atomCount)
    (firstMatching secondMatching : List (ℕ × ℕ)) : Prop :=
  maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges) =
      [firstMatching, secondMatching] ∧
    mol.mancudeEdgeMatchingPartnerZ attached.val firstMatching =
      mol.toMoleculeGraph.atomZ first ∧
    mol.mancudeEdgeMatchingPartnerZ attached.val secondMatching =
      mol.toMoleculeGraph.atomZ second

/-- Stronger odd certificate exposing the `k+k+1` partition of the actual maximum raw edge
matchings. -/
def OddCycleEdgeEnumerationCertificate (mol : RawMolecule)
    (attached : Fin mol.atomCount) (edges : List (ℕ × ℕ))
    (first second : Fin mol.atomCount) (k : ℕ)
    (firstFamily secondFamily : List (List (ℕ × ℕ)))
    (unmatched : List (ℕ × ℕ)) : Prop :=
  maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges) =
      firstFamily ++ secondFamily ++ [unmatched] ∧
    firstFamily.length = k ∧ secondFamily.length = k ∧
    (∀ matching ∈ firstFamily,
      mol.mancudeEdgeMatchingPartnerZ attached.val matching =
        mol.toMoleculeGraph.atomZ first) ∧
    (∀ matching ∈ secondFamily,
      mol.mancudeEdgeMatchingPartnerZ attached.val matching =
        mol.toMoleculeGraph.atomZ second) ∧
    mol.mancudeEdgeMatchingPartnerZ attached.val unmatched = 0

private theorem list_map_eq_replicate_of_forall {alpha beta : Type*}
    (items : List alpha) (field : alpha → beta) (value : beta)
    (hfield : ∀ item ∈ items, field item = value) :
    items.map field = List.replicate items.length value := by
  induction items with
  | nil => rfl
  | cons item items inductionHypothesis =>
      simp only [List.mem_cons, forall_eq_or_imp] at hfield
      rw [List.map_cons, hfield.1, inductionHypothesis hfield.2]
      exact List.replicate_succ.symm

/-- The exposed two-matching enumeration computes the compact even profile certificate. -/
theorem evenCycleMatchingCertificate_of_edgeEnumeration
    (mol : RawMolecule) (attached first second : Fin mol.atomCount)
    (edges firstMatching secondMatching : List (ℕ × ℕ))
    (henumeration : mol.EvenCycleEdgeEnumerationCertificate attached edges first second
      firstMatching secondMatching) :
    mol.EvenCycleMatchingCertificate attached edges first second := by
  rcases henumeration with ⟨hfamily, hfirst, hsecond⟩
  unfold EvenCycleMatchingCertificate executableMaximumPartnerProfile
  rw [hfamily]
  simp only [List.map_cons, List.map_nil, hfirst, hsecond]
  rfl

/-- The exposed `k+k+1` raw enumeration computes the compact odd profile certificate. -/
theorem oddCycleMatchingCertificate_of_edgeEnumeration
    (mol : RawMolecule) (attached first second : Fin mol.atomCount) (k : ℕ)
    (edges : List (ℕ × ℕ))
    (firstFamily secondFamily : List (List (ℕ × ℕ)))
    (unmatched : List (ℕ × ℕ))
    (henumeration : mol.OddCycleEdgeEnumerationCertificate attached edges first second k
      firstFamily secondFamily unmatched) :
    mol.OddCycleMatchingCertificate attached edges first second k := by
  rcases henumeration with
    ⟨hfamily, hfirstLength, hsecondLength, hfirst, hsecond, hunmatched⟩
  unfold OddCycleMatchingCertificate executableMaximumPartnerProfile
  rw [hfamily, List.map_append, List.map_append,
    list_map_eq_replicate_of_forall firstFamily
      (mol.mancudeEdgeMatchingPartnerZ attached.val)
      (mol.toMoleculeGraph.atomZ first) hfirst,
    list_map_eq_replicate_of_forall secondFamily
      (mol.mancudeEdgeMatchingPartnerZ attached.val)
      (mol.toMoleculeGraph.atomZ second) hsecond,
    hfirstLength, hsecondLength]
  simp only [List.map_cons, List.map_nil, hunmatched]
  change ((List.replicate k (mol.toMoleculeGraph.atomZ first) ++
      List.replicate k (mol.toMoleculeGraph.atomZ second) ++ [0] : List ℕ) : Multiset ℕ) = _
  rw [show ((List.replicate k (mol.toMoleculeGraph.atomZ first) ++
      List.replicate k (mol.toMoleculeGraph.atomZ second) ++ [0] : List ℕ) : Multiset ℕ) =
      (↑(List.replicate k (mol.toMoleculeGraph.atomZ first)) : Multiset ℕ) +
        (↑(List.replicate k (mol.toMoleculeGraph.atomZ second)) : Multiset ℕ) + {0} by rfl]
  rw [Multiset.coe_replicate, Multiset.coe_replicate]

private theorem maximumPartnerProfile_eq_independent
    (mol : RawMolecule) (attached : Fin mol.atomCount) (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges) :
    mol.executableMaximumPartnerProfile attached.val edges =
      (mol.toMoleculeGraph.maximumMancudeMatchings attached).1.map
        (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) := by
  classical
  let maximumEdges := maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges)
  let rawFinset := maximumEdges.toFinset
  let independent := mol.toMoleculeGraph.maximumMancudeMatchings attached
  let equivalence := maximumMancudeEdgeMatchingEquiv mol attached edges hrealizes
  have hmaximumNodup : maximumEdges.Nodup :=
    (exhaustiveMancudeEdgeMatchings_nodup edges hrealizes.nodup).sublist
      List.filter_sublist
  have hrawUniverse :
      (Finset.univ : Finset {matching // matching ∈ rawFinset}) = rawFinset.attach := by
    ext matching
    simp
  have hindependentUniverse :
      (Finset.univ : Finset {partner // partner ∈ independent}) = independent.attach := by
    ext partner
    simp
  have hcontribution : ∀ matching : {matching // matching ∈ rawFinset},
      mol.toMoleculeGraph.mancudePartnerAtomicNumber attached (equivalence matching).1 =
        mol.mancudeEdgeMatchingPartnerZ attached.val matching.1 := by
    intro matching
    have hmaximum := (mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges matching.1).1
      (List.mem_toFinset.1 matching.2)
    change mol.toMoleculeGraph.mancudePartnerAtomicNumber attached
        (partnerOfMancudeEdgeMatching matching.1) = _
    exact mancudePartnerAtomicNumber_partnerOfMancudeEdgeMatching
      mol attached matching.1 hmaximum.1.2
      (fun edge hedge => hrealizes.endpointsInBounds edge (hmaximum.1.1.subset hedge))
      (fun edge hedge => hrealizes.noSelfEdges edge (hmaximum.1.1.subset hedge))
  have huniverse := Multiset.map_univ_val_equiv equivalence
  have hmapped := congrArg
    (Multiset.map fun partner : {partner // partner ∈ independent} =>
      mol.toMoleculeGraph.mancudePartnerAtomicNumber attached partner.1) huniverse
  simp only [Multiset.map_map] at hmapped
  rw [hrawUniverse, hindependentUniverse] at hmapped
  simp only [Finset.attach_val, Function.comp_apply, hcontribution] at hmapped
  have hmapped' : rawFinset.1.map
        (mol.mancudeEdgeMatchingPartnerZ attached.val) =
      independent.1.map
        (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) := by
    have hrawAttach : rawFinset.1.attach.map
          (fun matching => mol.mancudeEdgeMatchingPartnerZ attached.val matching.val) =
        rawFinset.1.map (mol.mancudeEdgeMatchingPartnerZ attached.val) :=
      Multiset.attach_map_val' rawFinset.1 _
    have hindependentAttach : independent.1.attach.map
          (fun partner =>
            mol.toMoleculeGraph.mancudePartnerAtomicNumber attached partner.val) =
        independent.1.map
          (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) :=
      Multiset.attach_map_val' independent.1 _
    exact hrawAttach.symm.trans (hmapped.trans hindependentAttach)
  rw [← hmapped']
  simp only [executableMaximumPartnerProfile, rawFinset,
    List.toFinset_val, List.dedup_eq_self.mpr hmaximumNodup]
  rfl

/-- A certified raw even-cycle matching enumeration transports to the independent even profile. -/
theorem evenSimpleCycleProfile_of_matchingCertificate
    (mol : RawMolecule) (attached first second : Fin mol.atomCount)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hcertificate : mol.EvenCycleMatchingCertificate attached edges first second) :
    mol.toMoleculeGraph.EvenSimpleCycleProfile attached first second := by
  unfold MoleculeGraph.EvenSimpleCycleProfile
  rw [← maximumPartnerProfile_eq_independent mol attached edges hrealizes]
  exact hcertificate

/-- A certified raw odd-cycle matching enumeration transports to the independent odd profile. -/
theorem oddSimpleCycleProfile_of_matchingCertificate
    (mol : RawMolecule) (attached first second : Fin mol.atomCount) (k : ℕ)
    (edges : List (ℕ × ℕ))
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (hcertificate : mol.OddCycleMatchingCertificate attached edges first second k) :
    mol.toMoleculeGraph.OddSimpleCycleProfile attached first second k := by
  unfold MoleculeGraph.OddSimpleCycleProfile
  rw [← maximumPartnerProfile_eq_independent mol attached edges hrealizes]
  exact hcertificate

/-- End-to-end soundness of the production even-cycle formula from an explicit raw maximum-family
certificate, without assuming an independent profile. -/
theorem simpleMancudeCycle_even_sound_of_edgeEnumeration
    (mol : RawMolecule) (attached duplicated alternate : Fin mol.atomCount)
    (cycle : List ℕ) (edges firstMatching secondMatching : List (ℕ × ℕ))
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hcycle : mol.simpleMancudeCycle? attached.val duplicated.val =
      some (cycle, alternate.val))
    (heven : cycle.length % 2 = 0)
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (henumeration : mol.EvenCycleEdgeEnumerationCertificate attached edges
      duplicated alternate firstMatching secondMatching) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label ∧
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  have hcertificate := mol.evenCycleMatchingCertificate_of_edgeEnumeration
    attached duplicated alternate edges firstMatching secondMatching henumeration
  have hprofile := mol.evenSimpleCycleProfile_of_matchingCertificate
    attached duplicated alternate edges hrealizes hcertificate
  exact mol.simpleMancudeCycle_even_sound attached duplicated cycle alternate
    hlocalized hcycle heven hprofile

/-- End-to-end soundness of the production odd-cycle formula from an explicit raw `k+k+1`
maximum-family certificate, without assuming an independent profile. -/
theorem simpleMancudeCycle_odd_sound_of_edgeEnumeration
    (mol : RawMolecule) (attached duplicated alternate : Fin mol.atomCount)
    (cycle : List ℕ) (k : ℕ) (edges : List (ℕ × ℕ))
    (firstFamily secondFamily : List (List (ℕ × ℕ)))
    (unmatched : List (ℕ × ℕ))
    (hlocalized : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (hcycle : mol.simpleMancudeCycle? attached.val duplicated.val =
      some (cycle, alternate.val))
    (hlength : cycle.length = 2 * k + 1)
    (hrealizes : LocalizedMancudeEdgeListRealization mol attached edges)
    (henumeration : mol.OddCycleEdgeEnumerationCertificate attached edges
      duplicated alternate k firstFamily secondFamily unmatched) :
    ∃ label, mol.mancudeRule1aLabel? attached.val duplicated.val = some label ∧
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  have hcertificate := mol.oddCycleMatchingCertificate_of_edgeEnumeration
    attached duplicated alternate k edges firstFamily secondFamily unmatched henumeration
  have hprofile := mol.oddSimpleCycleProfile_of_matchingCertificate
    attached duplicated alternate k edges hrealizes hcertificate
  exact mol.simpleMancudeCycle_odd_sound attached duplicated cycle alternate k
    hlocalized hcycle hlength hprofile

end RawMolecule

end
end OneCenter
end TetraStereo
