import TetraStereo.OneCenter.DeclarativeCIPRule1aExact
import TetraStereo.OneCenter.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace MoleculeGraph

noncomputable section

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

theorem incidentDoubleBondCount_aut (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (atom : Atom) :
    molecule.incidentDoubleBondCount ((e : Equiv.Perm Atom) atom) =
      molecule.incidentDoubleBondCount atom := by
  classical
  unfold incidentDoubleBondCount
  let source := (Finset.univ : Finset Atom).filter fun other => molecule.bond atom other = 2
  let target := (Finset.univ : Finset Atom).filter fun other =>
    molecule.bond ((e : Equiv.Perm Atom) atom) other = 2
  change target.card = source.card
  symm
  apply Finset.card_bij (fun other _ => (e : Equiv.Perm Atom) other)
  · intro other hother
    have hbond := (Finset.mem_filter.1 hother).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa using (MoleculeGraph.Aut.bond_eq molecule e atom other).trans hbond
  · intro first _ second _ heq
    exact (e : Equiv.Perm Atom).injective heq
  · intro other hother
    refine ⟨(e : Equiv.Perm Atom).symm other, ?_, ?_⟩
    · apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      have hbond := (Finset.mem_filter.1 hother).2
      have hpreserved := MoleculeGraph.Aut.bond_eq molecule e atom
        ((e : Equiv.Perm Atom).symm other)
      have hp : molecule.bond ((e : Equiv.Perm Atom) atom) other =
          molecule.bond atom ((e : Equiv.Perm Atom).symm other) := by
        simpa using hpreserved
      exact hp.symm.trans hbond
    · simp

theorem localizedMancudeVertex_aut_iff (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (atom : Atom) :
    molecule.LocalizedMancudeVertex ((e : Equiv.Perm Atom) atom) ↔
      molecule.LocalizedMancudeVertex atom := by
  simp only [LocalizedMancudeVertex, molecule.incidentDoubleBondCount_aut e atom,
    MoleculeGraph.Aut.formalCharge_eq]

theorem mancudeCandidateEdge_aut_iff (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (left right : Atom) :
    molecule.MancudeCandidateEdge ((e : Equiv.Perm Atom) left)
        ((e : Equiv.Perm Atom) right) ↔
      molecule.MancudeCandidateEdge left right := by
  simp only [MancudeCandidateEdge, MoleculeGraph.Aut.bond_eq,
    molecule.localizedMancudeVertex_aut_iff e]

theorem mancudeStepWithout_aut_iff (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (blockedLeft blockedRight left right : Atom) :
    molecule.MancudeStepWithout ((e : Equiv.Perm Atom) blockedLeft)
        ((e : Equiv.Perm Atom) blockedRight)
        ((e : Equiv.Perm Atom) left) ((e : Equiv.Perm Atom) right) ↔
      molecule.MancudeStepWithout blockedLeft blockedRight left right := by
  rw [MancudeStepWithout, MancudeStepWithout,
    molecule.mancudeCandidateEdge_aut_iff e]
  simp only [Equiv.apply_eq_iff_eq, not_or, not_and]

private theorem map_reflTransGen_mancudeStepWithout
    (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (blockedLeft blockedRight left right : Atom) :
    Relation.ReflTransGen (molecule.MancudeStepWithout blockedLeft blockedRight) left right →
      Relation.ReflTransGen
        (molecule.MancudeStepWithout ((e : Equiv.Perm Atom) blockedLeft)
          ((e : Equiv.Perm Atom) blockedRight))
        ((e : Equiv.Perm Atom) left) ((e : Equiv.Perm Atom) right) := by
  intro hpath
  induction hpath with
  | refl => exact .refl
  | tail hpath hedge inductionHypothesis =>
      exact inductionHypothesis.tail
        ((molecule.mancudeStepWithout_aut_iff e _ _ _ _).2 hedge)

theorem localizedMancudeEdge_aut_iff (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (left right : Atom) :
    molecule.LocalizedMancudeEdge ((e : Equiv.Perm Atom) left)
        ((e : Equiv.Perm Atom) right) ↔
      molecule.LocalizedMancudeEdge left right := by
  constructor
  · intro h
    have hinverse : (e : Equiv.Perm Atom)⁻¹ ∈ molecule.Aut := Subgroup.inv_mem _ e.property
    let inverse : molecule.Aut := ⟨(e : Equiv.Perm Atom)⁻¹, hinverse⟩
    rcases h with ⟨hcandidate, hpath⟩
    refine ⟨(molecule.mancudeCandidateEdge_aut_iff e left right).1 hcandidate, ?_⟩
    simpa [inverse] using
      map_reflTransGen_mancudeStepWithout molecule inverse
        ((e : Equiv.Perm Atom) left) ((e : Equiv.Perm Atom) right)
        ((e : Equiv.Perm Atom) left) ((e : Equiv.Perm Atom) right) hpath
  · rintro ⟨hcandidate, hpath⟩
    exact ⟨(molecule.mancudeCandidateEdge_aut_iff e left right).2 hcandidate,
      map_reflTransGen_mancudeStepWithout molecule e left right left right hpath⟩

private theorem map_reflTransGen_localizedMancudeEdge
    (molecule : MoleculeGraph Atom) (e : molecule.Aut) (left right : Atom) :
    Relation.ReflTransGen molecule.LocalizedMancudeEdge left right →
      Relation.ReflTransGen molecule.LocalizedMancudeEdge
        ((e : Equiv.Perm Atom) left) ((e : Equiv.Perm Atom) right) := by
  intro hpath
  induction hpath with
  | refl => exact .refl
  | tail hpath hedge inductionHypothesis =>
      exact inductionHypothesis.tail
        ((molecule.localizedMancudeEdge_aut_iff e _ _).2 hedge)

theorem inMancudeComponent_aut_iff (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (attached atom : Atom) :
    molecule.InMancudeComponent ((e : Equiv.Perm Atom) attached)
        ((e : Equiv.Perm Atom) atom) ↔
      molecule.InMancudeComponent attached atom := by
  constructor
  · intro h
    have hinverse : (e : Equiv.Perm Atom)⁻¹ ∈ molecule.Aut := Subgroup.inv_mem _ e.property
    let inverse : molecule.Aut := ⟨(e : Equiv.Perm Atom)⁻¹, hinverse⟩
    simpa [inverse] using map_reflTransGen_localizedMancudeEdge molecule inverse
      ((e : Equiv.Perm Atom) attached) ((e : Equiv.Perm Atom) atom) h
  · exact map_reflTransGen_localizedMancudeEdge molecule e attached atom

/-- Conjugate a partner assignment by an atom automorphism. -/
def mancudePartnerEquiv (e : Equiv.Perm Atom) :
    (Atom → Option Atom) ≃ (Atom → Option Atom) where
  toFun := fun partner atom => (partner (e.symm atom)).map e
  invFun := fun partner atom => (partner (e atom)).map e.symm
  left_inv := by
    intro partner
    funext atom
    simp only [e.symm_apply_apply]
    cases partner atom <;> simp
  right_inv := by
    intro partner
    funext atom
    simp only [e.apply_symm_apply]
    cases partner atom <;> simp

omit [Fintype Atom] [DecidableEq Atom] in
private theorem option_map_perm_eq_some_iff (e : Equiv.Perm Atom)
    (value : Option Atom) (atom : Atom) :
    value.map e = some atom ↔ value = some (e.symm atom) := by
  cases value with
  | none => simp
  | some other =>
      simp only [Option.map_some, Option.some.injEq]
      exact e.eq_symm_apply.symm

omit [Fintype Atom] [DecidableEq Atom] in
@[simp] theorem mancudePartnerEquiv_apply (e : Equiv.Perm Atom)
    (partner : Atom → Option Atom) (atom : Atom) :
    mancudePartnerEquiv e partner (e atom) = (partner atom).map e := by
  simp [mancudePartnerEquiv]

theorem isMancudeMatching_partnerEquiv_iff (molecule : MoleculeGraph Atom)
    (e : molecule.Aut) (attached : Atom) (partner : Atom → Option Atom) :
    molecule.IsMancudeMatching ((e : Equiv.Perm Atom) attached)
        (mancudePartnerEquiv (e : Equiv.Perm Atom) partner) ↔
      molecule.IsMancudeMatching attached partner := by
  constructor
  · rintro ⟨houtside, hmatching⟩
    constructor
    · intro atom hcomponent
      have htarget : ¬ molecule.InMancudeComponent ((e : Equiv.Perm Atom) attached)
          ((e : Equiv.Perm Atom) atom) := by
        simpa [molecule.inMancudeComponent_aut_iff e attached atom] using hcomponent
      have := houtside ((e : Equiv.Perm Atom) atom) htarget
      simpa using this
    · intro left right
      have hlocal := hmatching ((e : Equiv.Perm Atom) left) ((e : Equiv.Perm Atom) right)
      simpa [molecule.localizedMancudeEdge_aut_iff e left right] using hlocal
  · rintro ⟨houtside, hmatching⟩
    constructor
    · intro atom hcomponent
      let source := (e : Equiv.Perm Atom).symm atom
      have hsource : ¬ molecule.InMancudeComponent attached source := by
        intro h
        have hmapped := (molecule.inMancudeComponent_aut_iff e attached source).2 h
        exact hcomponent (by simpa [source] using hmapped)
      have := houtside source hsource
      simpa [source, mancudePartnerEquiv] using
        congrArg (Option.map (e : Equiv.Perm Atom)) this
    · intro left right
      let sourceLeft := (e : Equiv.Perm Atom).symm left
      let sourceRight := (e : Equiv.Perm Atom).symm right
      have hlocal := hmatching sourceLeft sourceRight
      change (partner sourceLeft).map (e : Equiv.Perm Atom) = some right ↔
        (partner sourceRight).map (e : Equiv.Perm Atom) = some left ∧
          molecule.LocalizedMancudeEdge left right
      rw [option_map_perm_eq_some_iff, option_map_perm_eq_some_iff]
      have hedge : molecule.LocalizedMancudeEdge left right ↔
          molecule.LocalizedMancudeEdge sourceLeft sourceRight := by
        simpa [sourceLeft, sourceRight] using
          molecule.localizedMancudeEdge_aut_iff e sourceLeft sourceRight
      rw [hedge]
      simpa [sourceLeft, sourceRight] using hlocal

omit [DecidableEq Atom] in
theorem mancudeSaturation_partnerEquiv (e : Equiv.Perm Atom)
    (partner : Atom → Option Atom) :
    mancudeSaturation (mancudePartnerEquiv e partner) = mancudeSaturation partner := by
  classical
  unfold mancudeSaturation
  let source := (Finset.univ : Finset Atom).filter fun atom => (partner atom).isSome
  let target := (Finset.univ : Finset Atom).filter fun atom =>
    (mancudePartnerEquiv e partner atom).isSome
  change target.card = source.card
  symm
  apply Finset.card_bij (fun atom _ => e atom)
  · intro atom hatom
    have hsource : (partner atom).isSome := by simpa [source] using hatom
    simpa [target] using hsource
  · intro first _ second _ h
    exact e.injective h
  · intro atom hatom
    refine ⟨e.symm atom, ?_, by simp⟩
    have htarget : (mancudePartnerEquiv e partner atom).isSome := by
      simpa [target] using hatom
    simpa [source, mancudePartnerEquiv] using htarget

theorem isMaximumMancudeMatching_partnerEquiv_iff (molecule : MoleculeGraph Atom)
    (e : molecule.Aut) (attached : Atom) (partner : Atom → Option Atom) :
    molecule.IsMaximumMancudeMatching ((e : Equiv.Perm Atom) attached)
        (mancudePartnerEquiv (e : Equiv.Perm Atom) partner) ↔
      molecule.IsMaximumMancudeMatching attached partner := by
  constructor
  · rintro ⟨hmatching, hmaximum⟩
    refine ⟨(molecule.isMancudeMatching_partnerEquiv_iff e attached partner).1 hmatching, ?_⟩
    intro other hother
    let transported := mancudePartnerEquiv (e : Equiv.Perm Atom) other
    have htransported : molecule.IsMancudeMatching ((e : Equiv.Perm Atom) attached) transported :=
      (molecule.isMancudeMatching_partnerEquiv_iff e attached other).2 hother
    have hle := hmaximum transported htransported
    simpa [transported, mancudeSaturation_partnerEquiv] using hle
  · rintro ⟨hmatching, hmaximum⟩
    refine ⟨(molecule.isMancudeMatching_partnerEquiv_iff e attached partner).2 hmatching, ?_⟩
    intro other hother
    let source := (mancudePartnerEquiv (e : Equiv.Perm Atom)).symm other
    have hsource : molecule.IsMancudeMatching attached source := by
      have hback := (molecule.isMancudeMatching_partnerEquiv_iff e attached source).1
      exact hback (by simpa [source])
    have hle := hmaximum source hsource
    have hotherSat : mancudeSaturation other = mancudeSaturation source := by
      have := mancudeSaturation_partnerEquiv (e : Equiv.Perm Atom) source
      simpa [source] using this
    rw [mancudeSaturation_partnerEquiv]
    exact hotherSat.trans_le hle

theorem mancudePartnerAtomicNumber_partnerEquiv (molecule : MoleculeGraph Atom)
    (e : molecule.Aut) (attached : Atom) (partner : Atom → Option Atom) :
    molecule.mancudePartnerAtomicNumber ((e : Equiv.Perm Atom) attached)
        (mancudePartnerEquiv (e : Equiv.Perm Atom) partner) =
      molecule.mancudePartnerAtomicNumber attached partner := by
  unfold mancudePartnerAtomicNumber
  simp only [mancudePartnerEquiv_apply]
  cases hpartner : partner attached with
  | none => rfl
  | some atom =>
      simp [MoleculeGraph.Aut.atomZ_eq]

theorem exactMancudeAverage_aut (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (attached : Atom) :
    molecule.exactMancudeAverage ((e : Equiv.Perm Atom) attached) =
      molecule.exactMancudeAverage attached := by
  classical
  apply DeclarativeCIP.ExactAtomicNumber.ext
  · unfold exactMancudeAverage
    apply Finset.sum_bij
        (fun partner _ => mancudePartnerEquiv ((e : Equiv.Perm Atom).symm) partner)
    · intro partner hpartner
      simp only [maximumMancudeMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hpartner ⊢
      have hinverse : (e : Equiv.Perm Atom)⁻¹ ∈ molecule.Aut := Subgroup.inv_mem _ e.property
      let inverse : molecule.Aut := ⟨(e : Equiv.Perm Atom)⁻¹, hinverse⟩
      simpa [inverse, mancudePartnerEquiv] using
        (molecule.isMaximumMancudeMatching_partnerEquiv_iff inverse
          ((e : Equiv.Perm Atom) attached) partner).2 hpartner
    · intro first _ second _ heq
      exact (mancudePartnerEquiv ((e : Equiv.Perm Atom).symm)).injective heq
    · intro partner hpartner
      refine ⟨mancudePartnerEquiv (e : Equiv.Perm Atom) partner, ?_, ?_⟩
      · simp only [maximumMancudeMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hpartner ⊢
        exact (molecule.isMaximumMancudeMatching_partnerEquiv_iff e attached partner).2 hpartner
      · simp [mancudePartnerEquiv]
    · intro partner hpartner
      have hinverse : (e : Equiv.Perm Atom)⁻¹ ∈ molecule.Aut := Subgroup.inv_mem _ e.property
      let inverse : molecule.Aut := ⟨(e : Equiv.Perm Atom)⁻¹, hinverse⟩
      simpa [inverse, mancudePartnerEquiv] using
        (molecule.mancudePartnerAtomicNumber_partnerEquiv inverse
          ((e : Equiv.Perm Atom) attached) partner).symm
  · unfold exactMancudeAverage
    apply Finset.card_bij
        (fun partner _ => mancudePartnerEquiv ((e : Equiv.Perm Atom).symm) partner)
    · intro partner hpartner
      simp only [maximumMancudeMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hpartner ⊢
      have hinverse : (e : Equiv.Perm Atom)⁻¹ ∈ molecule.Aut := Subgroup.inv_mem _ e.property
      let inverse : molecule.Aut := ⟨(e : Equiv.Perm Atom)⁻¹, hinverse⟩
      simpa [inverse, mancudePartnerEquiv] using
        (molecule.isMaximumMancudeMatching_partnerEquiv_iff inverse
          ((e : Equiv.Perm Atom) attached) partner).2 hpartner
    · intro first _ second _ heq
      exact (mancudePartnerEquiv ((e : Equiv.Perm Atom).symm)).injective heq
    · intro partner hpartner
      refine ⟨mancudePartnerEquiv (e : Equiv.Perm Atom) partner, ?_, ?_⟩
      · simp only [maximumMancudeMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hpartner ⊢
        exact (molecule.isMaximumMancudeMatching_partnerEquiv_iff e attached partner).2 hpartner
      · simp [mancudePartnerEquiv]

theorem exactRule1aMultipleBond_aut (molecule : MoleculeGraph Atom) (e : molecule.Aut)
    (attached duplicated : Atom) :
    molecule.exactRule1aMultipleBond ((e : Equiv.Perm Atom) attached)
        ((e : Equiv.Perm Atom) duplicated) =
      molecule.exactRule1aMultipleBond attached duplicated := by
  classical
  by_cases hlocalized : molecule.LocalizedMancudeEdge attached duplicated
  · have hmapped : molecule.LocalizedMancudeEdge ((e : Equiv.Perm Atom) attached)
        ((e : Equiv.Perm Atom) duplicated) :=
      (molecule.localizedMancudeEdge_aut_iff e attached duplicated).2 hlocalized
    rw [molecule.exactRule1aMultipleBond_of_localized hmapped,
      molecule.exactRule1aMultipleBond_of_localized hlocalized,
      molecule.exactMancudeAverage_aut e attached]
  · have hmapped : ¬ molecule.LocalizedMancudeEdge ((e : Equiv.Perm Atom) attached)
        ((e : Equiv.Perm Atom) duplicated) := by
      simpa [molecule.localizedMancudeEdge_aut_iff e attached duplicated] using hlocalized
    rw [molecule.exactRule1aMultipleBond_of_not_localized hmapped,
      molecule.exactRule1aMultipleBond_of_not_localized hlocalized,
      MoleculeGraph.Aut.atomZ_eq]

theorem exactRule1aMultipleBond_outcome_aut_iff (molecule : MoleculeGraph Atom)
    (e : molecule.Aut) (leftAttached leftDuplicated rightAttached rightDuplicated : Atom)
    (outcome : Ordering) :
    DeclarativeCIP.ExactAtomicNumber.Outcome
        (molecule.exactRule1aMultipleBond ((e : Equiv.Perm Atom) leftAttached)
          ((e : Equiv.Perm Atom) leftDuplicated))
        (molecule.exactRule1aMultipleBond ((e : Equiv.Perm Atom) rightAttached)
          ((e : Equiv.Perm Atom) rightDuplicated)) outcome ↔
      DeclarativeCIP.ExactAtomicNumber.Outcome
        (molecule.exactRule1aMultipleBond leftAttached leftDuplicated)
        (molecule.exactRule1aMultipleBond rightAttached rightDuplicated) outcome := by
  rw [molecule.exactRule1aMultipleBond_aut e leftAttached leftDuplicated,
    molecule.exactRule1aMultipleBond_aut e rightAttached rightDuplicated]

end
end MoleculeGraph
end OneCenter
end TetraStereo
