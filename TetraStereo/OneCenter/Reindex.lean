import TetraStereo.OneCenter.CIPSymmetry
import TetraStereo.OneCenter.RS
import TetraStereo.OneCenter.SymmetryChiralityClass
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindex the ligand enumeration by a permutation of `Fin 4`.

This models the fact that the initial ligand numbering is arbitrary: only the underlying
neighbors matter. -/
def reindex (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) : OneCenterMolecule V where
  mol := m.mol
  center := m.center
  ligandAtom i := m.ligandAtom (τ i)
  ligandAtom_adj := by
    intro i
    simpa using m.ligandAtom_adj (τ i)
  ligandAtom_injective := by
    intro i j hij
    apply τ.injective
    exact m.ligandAtom_injective hij
  ligandAtom_surjective := by
    intro v hv
    rcases m.ligandAtom_surjective v hv with ⟨i, rfl⟩
    refine ⟨τ⁻¹ i, ?_⟩
    simp

@[simp] theorem reindex_mol (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).mol = m.mol := rfl

@[simp] theorem reindex_center (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).center = m.center := rfl

@[simp] theorem reindex_ligandAtom (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (m.reindex τ).ligandAtom i = m.ligandAtom (τ i) := rfl

@[simp] theorem reindex_one (m : OneCenterMolecule V) : m.reindex (1 : Equiv.Perm (Fin 4)) = m := by
  cases m
  rfl

/-- Under a relabeling of ligand indices, the induced ligand permutation conjugates accordingly. -/
theorem ligandPerm_reindex (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) (e : m.CenterAut) :
    (m.reindex τ).ligandPerm e = τ⁻¹ * m.ligandPerm e * τ := by
  classical
  ext i
  have hi : (m.reindex τ).ligandPerm e i = (τ⁻¹ * m.ligandPerm e * τ) i := by
    apply (m.reindex τ).ligandAtom_injective
    simp [OneCenterMolecule.reindex]
  simpa using congrArg Fin.val hi

theorem permHandedness_ligandPermHom_reindex (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) (e : m.CenterAut) :
    permHandedness ((m.reindex τ).ligandPermHom e) = permHandedness (m.ligandPermHom e) := by
  simpa [OneCenterMolecule.ligandPermHom, ligandPerm_reindex] using
    (permHandedness_conj_inv (σ := τ) (τ := m.ligandPermHom e))

theorem achiralBySymmetry_reindex_iff (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).AchiralBySymmetry ↔ m.AchiralBySymmetry := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have h := (m.permHandedness_ligandPermHom_reindex (τ := τ) (e := e))
    -- Transport the oddness certificate across reindexing.
    simpa [h] using he
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have h := (m.permHandedness_ligandPermHom_reindex (τ := τ) (e := e))
    simpa [h] using he

theorem chiralBySymmetry_reindex_iff (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).ChiralBySymmetry ↔ m.ChiralBySymmetry := by
  constructor
  · intro h e
    have h' := h e
    have ht := (m.permHandedness_ligandPermHom_reindex (τ := τ) (e := e))
    simpa [ht] using h'
  · intro h e
    have h' := h e
    have ht := (m.permHandedness_ligandPermHom_reindex (τ := τ) (e := e))
    simpa [ht] using h'

/-- The CIP key is equivariant under ligand reindexing. -/
@[simp] theorem cipKey_reindex (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (m.reindex τ).cipKey i = m.cipKey (τ i) := by
  simp [OneCenterMolecule.cipKey, OneCenterMolecule.reindex]

theorem stereogenicByCIP_reindex_iff (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).StereogenicByCIP ↔ m.StereogenicByCIP := by
  constructor
  · intro h i j hij
    have hij' :
        (m.reindex τ).cipKey (τ⁻¹ i) = (m.reindex τ).cipKey (τ⁻¹ j) := by
      simpa using hij
    have : τ⁻¹ i = τ⁻¹ j := h hij'
    have := congrArg τ this
    simpa using this
  · intro h i j hij
    have hij' : m.cipKey (τ i) = m.cipKey (τ j) := by
      simpa using hij
    have : τ i = τ j := h hij'
    exact τ.injective this

theorem cipKeyWithTie_le_iff_cipKey_le_of_stereogenicByCIP (m : OneCenterMolecule V)
    (hst : m.StereogenicByCIP) (i j : Fin 4) :
    m.cipKeyWithTie j ≤ m.cipKeyWithTie i ↔ m.cipKey j ≤ m.cipKey i := by
  constructor
  · intro h
    have h' : m.cipKey j ≤ m.cipKey i ∧ (m.cipKey j = m.cipKey i → j ≤ i) := by
      simpa [OneCenterMolecule.cipKeyWithTie] using
        (Prod.Lex.toLex_le_toLex' (x := (m.cipKey j, j)) (y := (m.cipKey i, i))).1 h
    exact h'.1
  · intro hji
    have hImp : m.cipKey j = m.cipKey i → j ≤ i := by
      intro heq
      have : j = i := hst heq
      simp [this]
    have h' : m.cipKey j ≤ m.cipKey i ∧ (m.cipKey j = m.cipKey i → j ≤ i) :=
      ⟨hji, hImp⟩
    have :
        toLex (m.cipKey j, j) ≤ toLex (m.cipKey i, i) :=
      (Prod.Lex.toLex_le_toLex' (x := (m.cipKey j, j)) (y := (m.cipKey i, i))).2 h'
    simpa [OneCenterMolecule.cipKeyWithTie] using this

theorem cipOrder_reindex_of_stereogenicByCIP (m : OneCenterMolecule V) (hst : m.StereogenicByCIP)
    (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).cipOrder = m.cipOrder.map (τ⁻¹ : Equiv.Perm (Fin 4)) := by
  classical
  let m' : OneCenterMolecule V := m.reindex τ
  let r : Fin 4 → Fin 4 → Prop := fun i j => m.cipKeyWithTie j ≤ m.cipKeyWithTie i
  let r' : Fin 4 → Fin 4 → Prop := fun i j => m'.cipKeyWithTie j ≤ m'.cipKeyWithTie i

  haveI : IsTrans (Fin 4) r :=
    ⟨by
      intro a b c hab hbc
      exact le_trans hbc hab⟩
  haveI : Std.Total r :=
    ⟨by
      intro a b
      -- `key b ≤ key a ∨ key a ≤ key b`.
      simpa [r, or_comm] using le_total (m.cipKeyWithTie a) (m.cipKeyWithTie b)⟩

  haveI : IsTrans (Fin 4) r' :=
    ⟨by
      intro a b c hab hbc
      exact le_trans hbc hab⟩
  haveI : Std.Total r' :=
    ⟨by
      intro a b
      simpa [r', or_comm] using le_total (m'.cipKeyWithTie a) (m'.cipKeyWithTie b)⟩

  have hTieInj : Function.Injective m'.cipKeyWithTie := by
    intro i j hij
    have hpair : (m'.cipKey i, i) = (m'.cipKey j, j) := by
      exact toLex.injective (by simpa [OneCenterMolecule.cipKeyWithTie] using hij)
    exact congrArg Prod.snd hpair

  haveI : Std.Antisymm r' :=
    ⟨by
      intro a b hab hba
      have hEq : m'.cipKeyWithTie a = m'.cipKeyWithTie b := le_antisymm hba hab
      exact hTieInj hEq⟩

  have hpair' : m'.cipOrder.Pairwise r' := by
    simpa [OneCenterMolecule.cipOrder, r', m'] using
      (List.pairwise_mergeSort' (r := r') (List.finRange 4))

  have hpair : m.cipOrder.Pairwise r := by
    simpa [OneCenterMolecule.cipOrder, r] using
      (List.pairwise_mergeSort' (r := r) (List.finRange 4))

  have hst' : m'.StereogenicByCIP :=
    (m.stereogenicByCIP_reindex_iff (τ := τ)).2 hst

  have hmapRel : ∀ a b : Fin 4, r a b → r' (τ⁻¹ a) (τ⁻¹ b) := by
    intro a b hab
    have habKey : m.cipKey b ≤ m.cipKey a :=
      (m.cipKeyWithTie_le_iff_cipKey_le_of_stereogenicByCIP (hst := hst) (i := a) (j := b)).1 hab
    have habKey' : m'.cipKey (τ⁻¹ b) ≤ m'.cipKey (τ⁻¹ a) := by
      simpa [m', OneCenterMolecule.cipKey_reindex] using habKey
    have habTie' : m'.cipKeyWithTie (τ⁻¹ b) ≤ m'.cipKeyWithTie (τ⁻¹ a) :=
      (m'.cipKeyWithTie_le_iff_cipKey_le_of_stereogenicByCIP (hst := hst') (i := τ⁻¹ a)
          (j := τ⁻¹ b)).2 habKey'
    simpa [r'] using habTie'

  have hpairMap : (m.cipOrder.map (τ⁻¹ : Equiv.Perm (Fin 4))).Pairwise r' :=
    (hpair.map (f := (τ⁻¹ : Equiv.Perm (Fin 4))) (H := hmapRel))

  have hperm₁ : m'.cipOrder.Perm (List.finRange 4) :=
    m'.cipOrder_perm_finRange
  have hperm₂ : (m.cipOrder.map (τ⁻¹ : Equiv.Perm (Fin 4))).Perm (List.finRange 4) := by
    have hpermMap :
        (m.cipOrder.map (τ⁻¹ : Equiv.Perm (Fin 4))).Perm
          ((List.finRange 4).map (τ⁻¹ : Equiv.Perm (Fin 4))) :=
      (m.cipOrder_perm_finRange.map (τ⁻¹ : Equiv.Perm (Fin 4)))
    have hpermFin : ((List.finRange 4).map (τ⁻¹ : Equiv.Perm (Fin 4))).Perm (List.finRange 4) := by
      simpa using (Equiv.Perm.map_finRange_perm (σ := (τ⁻¹ : Equiv.Perm (Fin 4))))
    exact hpermMap.trans hpermFin
  have hperm : m'.cipOrder.Perm (m.cipOrder.map (τ⁻¹ : Equiv.Perm (Fin 4))) :=
    hperm₁.trans hperm₂.symm

  exact (List.Perm.eq_of_pairwise' hpair' hpairMap hperm)

theorem cipPermutation_reindex_of_stereogenicByCIP (m : OneCenterMolecule V)
    (hst : m.StereogenicByCIP) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).cipPermutation = τ⁻¹ * m.cipPermutation := by
  classical
  have horder :
      (m.reindex τ).cipOrder = m.cipOrder.map (τ⁻¹ : Equiv.Perm (Fin 4)) :=
    m.cipOrder_reindex_of_stereogenicByCIP hst τ
  ext i
  -- Reduce both permutations to `List.get` on the CIP ordering list.
  -- `List.get` is phrased in terms of `Fin`; use `getElem` simp lemmas to see through `map`.
  simp [OneCenterMolecule.cipPermutation, horder, Equiv.Perm.mul_apply, List.get_eq_getElem,
    List.getElem_map]

/-- The cycle-cut CIP key is equivariant under ligand reindexing. -/
@[simp] theorem cipKeyCycleCut_reindex
    (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (m.reindex τ).cipKeyCycleCut i = m.cipKeyCycleCut (τ i) := by
  simp [OneCenterMolecule.cipKeyCycleCut, OneCenterMolecule.reindex]

theorem stereogenicByCIPCycleCut_reindex_iff
    (m : OneCenterMolecule V) (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).StereogenicByCIPCycleCut ↔ m.StereogenicByCIPCycleCut := by
  constructor
  · intro h i j hij
    have hij' :
        (m.reindex τ).cipKeyCycleCut (τ⁻¹ i) =
          (m.reindex τ).cipKeyCycleCut (τ⁻¹ j) := by
      simpa using hij
    have : τ⁻¹ i = τ⁻¹ j := h hij'
    have := congrArg τ this
    simpa using this
  · intro h i j hij
    have hij' : m.cipKeyCycleCut (τ i) = m.cipKeyCycleCut (τ j) := by
      simpa using hij
    have : τ i = τ j := h hij'
    exact τ.injective this

theorem cipKeyWithTieCycleCut_le_iff_cipKeyCycleCut_le_of_stereogenicByCIPCycleCut
    (m : OneCenterMolecule V) (hst : m.StereogenicByCIPCycleCut) (i j : Fin 4) :
    m.cipKeyWithTieCycleCut j ≤ m.cipKeyWithTieCycleCut i ↔
      m.cipKeyCycleCut j ≤ m.cipKeyCycleCut i := by
  constructor
  · intro h
    have h' :
        m.cipKeyCycleCut j ≤ m.cipKeyCycleCut i ∧
          (m.cipKeyCycleCut j = m.cipKeyCycleCut i → j ≤ i) := by
      simpa [OneCenterMolecule.cipKeyWithTieCycleCut] using
        (Prod.Lex.toLex_le_toLex'
          (x := (m.cipKeyCycleCut j, j)) (y := (m.cipKeyCycleCut i, i))).1 h
    exact h'.1
  · intro hji
    have hImp : m.cipKeyCycleCut j = m.cipKeyCycleCut i → j ≤ i := by
      intro heq
      have : j = i := hst heq
      simp [this]
    have h' :
        m.cipKeyCycleCut j ≤ m.cipKeyCycleCut i ∧
          (m.cipKeyCycleCut j = m.cipKeyCycleCut i → j ≤ i) :=
      ⟨hji, hImp⟩
    have :
        toLex (m.cipKeyCycleCut j, j) ≤ toLex (m.cipKeyCycleCut i, i) :=
      (Prod.Lex.toLex_le_toLex'
        (x := (m.cipKeyCycleCut j, j)) (y := (m.cipKeyCycleCut i, i))).2 h'
    simpa [OneCenterMolecule.cipKeyWithTieCycleCut] using this

theorem cipOrderCycleCut_reindex_of_stereogenicByCIPCycleCut
    (m : OneCenterMolecule V) (hst : m.StereogenicByCIPCycleCut)
    (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).cipOrderCycleCut =
      m.cipOrderCycleCut.map (τ⁻¹ : Equiv.Perm (Fin 4)) := by
  classical
  let m' : OneCenterMolecule V := m.reindex τ
  let r : Fin 4 → Fin 4 → Prop := fun i j =>
    m.cipKeyWithTieCycleCut j ≤ m.cipKeyWithTieCycleCut i
  let r' : Fin 4 → Fin 4 → Prop := fun i j =>
    m'.cipKeyWithTieCycleCut j ≤ m'.cipKeyWithTieCycleCut i

  haveI : IsTrans (Fin 4) r :=
    ⟨by
      intro a b c hab hbc
      exact le_trans hbc hab⟩
  haveI : Std.Total r :=
    ⟨by
      intro a b
      simpa [r, or_comm] using le_total (m.cipKeyWithTieCycleCut a) (m.cipKeyWithTieCycleCut b)⟩

  haveI : IsTrans (Fin 4) r' :=
    ⟨by
      intro a b c hab hbc
      exact le_trans hbc hab⟩
  haveI : Std.Total r' :=
    ⟨by
      intro a b
      simpa [r', or_comm] using le_total (m'.cipKeyWithTieCycleCut a) (m'.cipKeyWithTieCycleCut b)⟩

  have hTieInj : Function.Injective m'.cipKeyWithTieCycleCut := by
    intro i j hij
    have hpair : (m'.cipKeyCycleCut i, i) = (m'.cipKeyCycleCut j, j) := by
      exact toLex.injective (by simpa [OneCenterMolecule.cipKeyWithTieCycleCut] using hij)
    exact congrArg Prod.snd hpair

  haveI : Std.Antisymm r' :=
    ⟨by
      intro a b hab hba
      have hEq : m'.cipKeyWithTieCycleCut a = m'.cipKeyWithTieCycleCut b := le_antisymm hba hab
      exact hTieInj hEq⟩

  have hpair' : m'.cipOrderCycleCut.Pairwise r' := by
    simpa [OneCenterMolecule.cipOrderCycleCut, r', m'] using
      (List.pairwise_mergeSort' (r := r') (List.finRange 4))

  have hpair : m.cipOrderCycleCut.Pairwise r := by
    simpa [OneCenterMolecule.cipOrderCycleCut, r] using
      (List.pairwise_mergeSort' (r := r) (List.finRange 4))

  have hst' : m'.StereogenicByCIPCycleCut :=
    (m.stereogenicByCIPCycleCut_reindex_iff (τ := τ)).2 hst

  have hmapRel : ∀ a b : Fin 4, r a b → r' (τ⁻¹ a) (τ⁻¹ b) := by
    intro a b hab
    have habKey : m.cipKeyCycleCut b ≤ m.cipKeyCycleCut a :=
      (m.cipKeyWithTieCycleCut_le_iff_cipKeyCycleCut_le_of_stereogenicByCIPCycleCut
        (hst := hst) (i := a) (j := b)).1 hab
    have habKey' : m'.cipKeyCycleCut (τ⁻¹ b) ≤ m'.cipKeyCycleCut (τ⁻¹ a) := by
      simpa [m', OneCenterMolecule.cipKeyCycleCut_reindex] using habKey
    have habTie' : m'.cipKeyWithTieCycleCut (τ⁻¹ b) ≤
        m'.cipKeyWithTieCycleCut (τ⁻¹ a) :=
      (m'.cipKeyWithTieCycleCut_le_iff_cipKeyCycleCut_le_of_stereogenicByCIPCycleCut
        (hst := hst') (i := τ⁻¹ a) (j := τ⁻¹ b)).2 habKey'
    simpa [r'] using habTie'

  have hpairMap : (m.cipOrderCycleCut.map (τ⁻¹ : Equiv.Perm (Fin 4))).Pairwise r' :=
    hpair.map (f := (τ⁻¹ : Equiv.Perm (Fin 4))) (H := hmapRel)

  have hperm₁ : m'.cipOrderCycleCut.Perm (List.finRange 4) :=
    m'.cipOrderCycleCut_perm_finRange
  have hperm₂ : (m.cipOrderCycleCut.map (τ⁻¹ : Equiv.Perm (Fin 4))).Perm (List.finRange 4) := by
    have hpermMap :
        (m.cipOrderCycleCut.map (τ⁻¹ : Equiv.Perm (Fin 4))).Perm
          ((List.finRange 4).map (τ⁻¹ : Equiv.Perm (Fin 4))) :=
      m.cipOrderCycleCut_perm_finRange.map (τ⁻¹ : Equiv.Perm (Fin 4))
    have hpermFin : ((List.finRange 4).map (τ⁻¹ : Equiv.Perm (Fin 4))).Perm
        (List.finRange 4) := by
      simpa using (Equiv.Perm.map_finRange_perm (σ := (τ⁻¹ : Equiv.Perm (Fin 4))))
    exact hpermMap.trans hpermFin
  have hperm : m'.cipOrderCycleCut.Perm
      (m.cipOrderCycleCut.map (τ⁻¹ : Equiv.Perm (Fin 4))) :=
    hperm₁.trans hperm₂.symm

  exact (List.Perm.eq_of_pairwise' hpair' hpairMap hperm)

theorem cipPermutationCycleCut_reindex_of_stereogenicByCIPCycleCut
    (m : OneCenterMolecule V) (hst : m.StereogenicByCIPCycleCut)
    (τ : Equiv.Perm (Fin 4)) :
    (m.reindex τ).cipPermutationCycleCut = τ⁻¹ * m.cipPermutationCycleCut := by
  classical
  have horder :
      (m.reindex τ).cipOrderCycleCut =
        m.cipOrderCycleCut.map (τ⁻¹ : Equiv.Perm (Fin 4)) :=
    m.cipOrderCycleCut_reindex_of_stereogenicByCIPCycleCut hst τ
  ext i
  simp [OneCenterMolecule.cipPermutationCycleCut, horder, Equiv.Perm.mul_apply,
    List.get_eq_getElem, List.getElem_map]

theorem rs_reindex_of_stereogenicByCIP (m : OneCenterMolecule V) (hst : m.StereogenicByCIP)
    (τ : Equiv.Perm (Fin 4)) (g : TetrahedralGeometry.Realization) :
    (m.reindex τ).rs (TetrahedralGeometry.Realization.reindex g τ) = m.rs g := by
  classical
  have hperm :
      (m.reindex τ).cipPermutation = τ⁻¹ * m.cipPermutation :=
    m.cipPermutation_reindex_of_stereogenicByCIP hst τ
  have hhand :
      TetrahedralGeometry.handedness
          (TetrahedralGeometry.reindex
            (TetrahedralGeometry.reindex g.1 τ) (τ⁻¹ * m.cipPermutation)) =
        TetrahedralGeometry.handedness (TetrahedralGeometry.reindex g.1 m.cipPermutation) := by
    have h :=
      congrArg (fun r : TetrahedralGeometry.Realization => TetrahedralGeometry.handedness r.1)
        (TetrahedralGeometry.Realization.reindex_mul (g := g) (σ := τ) (τ := τ⁻¹ * m.cipPermutation))
    simp [TetrahedralGeometry.Realization.reindex, TetrahedralGeometry.reindex] at h ⊢
  -- The physical realization is unchanged; only the indexing changes.
  simp [OneCenterMolecule.rs, hperm, hhand]

theorem rsCycleCut_reindex_of_stereogenicByCIPCycleCut
    (m : OneCenterMolecule V) (hst : m.StereogenicByCIPCycleCut)
    (τ : Equiv.Perm (Fin 4)) (g : TetrahedralGeometry.Realization) :
    (m.reindex τ).rsCycleCut (TetrahedralGeometry.Realization.reindex g τ) =
      m.rsCycleCut g := by
  classical
  have hperm :
      (m.reindex τ).cipPermutationCycleCut = τ⁻¹ * m.cipPermutationCycleCut :=
    m.cipPermutationCycleCut_reindex_of_stereogenicByCIPCycleCut hst τ
  have hhand :
      TetrahedralGeometry.handedness
          (TetrahedralGeometry.reindex
            (TetrahedralGeometry.reindex g.1 τ) (τ⁻¹ * m.cipPermutationCycleCut)) =
        TetrahedralGeometry.handedness
          (TetrahedralGeometry.reindex g.1 m.cipPermutationCycleCut) := by
    have h :=
      congrArg (fun r : TetrahedralGeometry.Realization => TetrahedralGeometry.handedness r.1)
        (TetrahedralGeometry.Realization.reindex_mul
          (g := g) (σ := τ) (τ := τ⁻¹ * m.cipPermutationCycleCut))
    simp [TetrahedralGeometry.Realization.reindex, TetrahedralGeometry.reindex] at h ⊢
  simp [OneCenterMolecule.rsCycleCut, hperm, hhand]

end OneCenterMolecule

end
end OneCenter
end TetraStereo
