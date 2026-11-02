import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.UniversalProof.GeneralParserStateBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

theorem rule2Mass_carbon : ∃ mass, RawMolecule.rule2MassPico? Element.C none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 6 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem rule2Mass_hydrogen : ∃ mass, RawMolecule.rule2MassPico? Element.H none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 1 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem rule2Mass_fluorine : ∃ mass, RawMolecule.rule2MassPico? Element.F none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 9 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem rule2Mass_bromine : ∃ mass, RawMolecule.rule2MassPico? Element.Br none = some mass := by
  obtain ⟨mass, h⟩ := CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 35 (by decide)
  exact ⟨mass, by simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using h⟩

theorem ParsedBondKind.order_pos (k : ParsedBondKind) : 0 < k.order := by cases k <;> decide

theorem directedConnects_true_iff (bond : RawBond) (u v : ℕ) :
    bond.directedConnects u v = true ↔ bond.source = u ∧ bond.target = v := by
  unfold RawBond.directedConnects
  simp [Bool.and_eq_true]

theorem le_foldl (bonds : List RawBond) (u v a : ℕ) :
    a ≤ bonds.foldl (fun acc bond => if bond.directedConnects u v then max acc bond.kind.order else acc) a := by
  induction bonds generalizing a with
  | nil => exact le_rfl
  | cons bond rest ih =>
      simp only [List.foldl_cons]
      refine le_trans ?_ (ih _)
      by_cases hc : bond.directedConnects u v = true
      · rw [if_pos hc]; exact le_max_left _ _
      · rw [if_neg hc]

theorem foldl_pos_of_mem {bonds : List RawBond} {u v : ℕ} {b : RawBond}
    (hb : b ∈ bonds) (hs : b.source = u) (ht : b.target = v) :
    0 < bonds.foldl (fun acc bond => if bond.directedConnects u v then max acc bond.kind.order else acc) 0 := by
  induction bonds with
  | nil => simp at hb
  | cons head rest ih =>
      rcases List.mem_cons.mp hb with equal | hb'
      · subst b
        simp only [List.foldl_cons]
        have hc : head.directedConnects u v = true := (directedConnects_true_iff head u v).mpr ⟨hs, ht⟩
        rw [if_pos hc]
        exact lt_of_lt_of_le (ParsedBondKind.order_pos head.kind)
          (le_trans (le_max_right 0 _) (le_foldl rest u v _))
      · simp only [List.foldl_cons]
        by_cases hc : head.directedConnects u v = true
        · rw [if_pos hc]
          exact lt_of_lt_of_le (ParsedBondKind.order_pos head.kind)
            (le_trans (le_max_right 0 _) (le_foldl rest u v _))
        · rw [if_neg hc]
          exact ih hb'

theorem exists_of_fold_pos : ∀ {bonds : List RawBond} {u v : ℕ},
    0 < bonds.foldl (fun acc bond => if bond.directedConnects u v then max acc bond.kind.order else acc) 0 →
      ∃ b ∈ bonds, b.source = u ∧ b.target = v
  | [], _, _ => by intro h; simp at h
  | head :: rest, u, v => by
      intro h
      simp only [List.foldl_cons] at h
      by_cases hc : head.directedConnects u v = true
      · exact ⟨head, List.mem_cons_self, (directedConnects_true_iff head u v).mp hc⟩
      · rw [if_neg hc] at h
        obtain ⟨bond, member, source, target⟩ := exists_of_fold_pos (bonds := rest) h
        exact ⟨bond, List.mem_cons_of_mem head member, source, target⟩

theorem directedBondOrder_pos_of_connect (mol : RawMolecule) (b : RawBond) (hb : b ∈ mol.bonds)
    {u v : ℕ} (hs : b.source = u) (ht : b.target = v) : 0 < mol.directedBondOrder u v := by
  unfold RawMolecule.directedBondOrder
  exact foldl_pos_of_mem hb hs ht

theorem exists_connecting_of_directedBondOrder_pos (mol : RawMolecule) {u v : ℕ}
    (h : 0 < mol.directedBondOrder u v) :
    ∃ b ∈ mol.bonds, b.source = u ∧ b.target = v := by
  unfold RawMolecule.directedBondOrder at h
  exact exists_of_fold_pos h

end TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery

namespace TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

/-- Actual incident record projection, before the production graph-neighbor deduplication. -/
def recordNeighbor? (center : ℕ) (bond : RawBond) : Option ℕ :=
  if bond.source == center then some bond.target
  else if bond.target == center then some bond.source else none

def recordNeighbors (molecule : RawMolecule) (center : ℕ) : List ℕ :=
  molecule.bonds.filterMap (recordNeighbor? center)

end TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

namespace TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.GeneralParserStateBridge

theorem atomSpec_known_element (kind : FamilyAtom) :
    (atomSpec kind).element ≠ .wildcard := by
  cases kind <;> intro impossible <;> cases impossible

theorem atomSpec_mass_known (kind : FamilyAtom) :
    ∃ mass, RawMolecule.rule2MassPico? (atomSpec kind).element
      (atomSpec kind).isotope? = some mass := by
  cases kind with
  | hydrogen => exact NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery.rule2Mass_hydrogen
  | carbon => exact NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery.rule2Mass_carbon
  | taggedCarbon parity => exact NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery.rule2Mass_carbon
  | fluorine => exact NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery.rule2Mass_fluorine
  | bromine => exact NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery.rule2Mass_bromine

end TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge
