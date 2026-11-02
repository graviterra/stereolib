import TetraStereo.UniversalProof.NextFrontier.NativeNitrileParserPhysicalJoin
import TetraStereo.UniversalProof.NextFrontier.NativeNitrilePhysicalAdmission

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

private theorem append_lookup {Alpha : Type} (left right : List Alpha) (index : Nat) :
    (left ++ right)[left.length + index]? = right[index]? := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      rw [List.cons_append, List.length_cons]
      rw [show tail.length + 1 + index = (tail.length + index) + 1 by omega]
      rw [List.getElem?_cons_succ]
      exact ih

theorem raw_tail_written_row (parity : TetrahedralInputParity) (n offset : Nat)
    (bound : offset < n + 1) :
    (raw parity n).writtenNeighbors (offset + 6) =
      [tailParent offset] ++ if offset < n then [offset + 7] else [] := by
  have lookup : (raw parity n).neighborOrder[offset + 6]? =
      some ([tailParent offset] ++ if offset < n then [offset + 7] else []) := by
    change (completedPrefixRows ++ tailRows n)[offset + 6]? = _
    rw [show offset + 6 = completedPrefixRows.length + offset by
      simp [completedPrefixRows]; omega]
    rw [append_lookup]
    exact getElem?_map_range _ _ _ bound
  unfold writtenNeighbors
  rw [lookup]

theorem raw_tail_predecessor (parity : TetrahedralInputParity) (n offset : Nat)
    (bound : offset < n + 1) :
    (raw parity n).introductionPredecessors[offset + 6]? = some (some (tailParent offset)) := by
  change (introductionRows n)[offset + 6]? = _
  unfold introductionRows
  rw [show offset + 6 =
    ([none, some 0, some 0, some 2, some 0, some 4] : List (Option Nat)).length + offset by
      simp; omega]
  rw [append_lookup]
  exact getElem?_map_range _ _ _ bound

theorem raw_introduction_count (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).introductionPredecessors.length = (raw parity n).atomCount := by
  rw [raw_atomCount]
  exact introduction_rows_length n

private theorem intro_entry_valid (mol : RawMolecule) (index parent : Nat)
    (earlier : parent < index)
    (lookup : mol.introductionPredecessors[index]? = some (some parent))
    (head : (mol.writtenNeighbors index).head? = some parent)
    (edge : ∃ bond ∈ mol.bonds, bond.source = parent ∧ bond.target = index) :
    (match mol.introductionPredecessors[index]? with
      | none => false
      | some none => true
      | some (some previous) =>
          decide (previous < index) &&
            mol.bonds.any (fun bond => bond.source == previous && bond.target == index) &&
              ((mol.writtenNeighbors index).head? == some previous)) = true := by
  rw [lookup]
  simp only [earlier, decide_true, Bool.true_and, head, beq_self_eq_true, Bool.and_true]
  obtain ⟨bond, retained, source, target⟩ := edge
  exact List.any_eq_true.mpr ⟨bond, retained, by simp [source, target]⟩

theorem raw_introduction_valid (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).introductionPredecessorsValid? = true := by
  unfold introductionPredecessorsValid?
  rw [raw_introduction_count]
  simp only [Nat.le_refl, decide_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro index bound
  rw [raw_atomCount] at bound
  rcases lt_or_ge index 6 with small | large
  · interval_cases index
    · rfl
    · apply intro_entry_valid (raw parity n) 1 0 (by decide) rfl rfl
      exact ⟨⟨0, 1, .single⟩, by simp [raw, prefixBonds], rfl, rfl⟩
    · apply intro_entry_valid (raw parity n) 2 0 (by decide) rfl rfl
      exact ⟨⟨0, 2, .single⟩, by simp [raw, prefixBonds], rfl, rfl⟩
    · apply intro_entry_valid (raw parity n) 3 2 (by decide) rfl rfl
      exact ⟨⟨2, 3, .triple⟩, raw_triple_present parity n, rfl, rfl⟩
    · apply intro_entry_valid (raw parity n) 4 0 (by decide) rfl rfl
      exact ⟨⟨0, 4, .single⟩, by simp [raw, prefixBonds], rfl, rfl⟩
    · apply intro_entry_valid (raw parity n) 5 4 (by decide) rfl rfl
      exact ⟨⟨4, 5, .single⟩, by simp [raw, prefixBonds], rfl, rfl⟩
  · obtain ⟨offset, rfl⟩ : ∃ offset, index = offset + 6 := ⟨index - 6, by omega⟩
    have inside : offset < n + 1 := by omega
    apply intro_entry_valid (raw parity n) _ (tailParent offset) (tail_parent_lt offset)
      (raw_tail_predecessor parity n offset inside)
    · rw [raw_tail_written_row parity n offset inside]
      rfl
    · refine ⟨⟨tailParent offset, offset + 6, .single⟩, ?_, rfl, rfl⟩
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨offset, List.mem_range.mpr inside, rfl⟩

theorem raw_parser_introduction_valid (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).parserIntroductionValid? = true := by
  simp [parserIntroductionValid?, raw_introduction_count, raw_introduction_valid]

theorem raw_normalization_identity (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).normalizeUnspecifiedBonds = raw parity n := by
  have normalized : ∀ bonds : List RawBond,
      (∀ bond ∈ bonds, bond.kind = .single ∨ bond.kind = .triple) →
      bonds.map (raw parity n).normalizeUnspecifiedBond = bonds := by
    intro bonds kinds
    induction bonds with
    | nil => rfl
    | cons head tail ih =>
        have fixed : (raw parity n).normalizeUnspecifiedBond head = head := by
          rcases kinds head List.mem_cons_self with single | triple
          · simp [normalizeUnspecifiedBond, single]
          · simp [normalizeUnspecifiedBond, triple]
        rw [List.map_cons, fixed, ih (fun bond retained => kinds bond (List.mem_cons_of_mem head retained))]
  unfold normalizeUnspecifiedBonds
  rw [normalized _ (raw_bond_kinds parity n)]

theorem actual_finalized (parity : TetrahedralInputParity) (n : Nat) :
    finalizeParseState (finalState parity n) = .ok (raw parity n) := by
  have closed := actual_final_state_closed parity n
  have admitted : (raw parity n).admissible? = true :=
    (admissible?_eq_true_iff _).mpr (raw_admissible parity n)
  simp [finalizeParseState, closed.1, closed.2.1, closed.2.2,
    actual_final_state_molecule, raw_normalization_identity, admitted]

/-- Every natural chain length and either parity reaches the independent raw molecule through
the actual grammar, parser trace, structural finalizer and introduction-provenance guards. -/
theorem actual_parse (parity : TetrahedralInputParity) (n : Nat) :
    parseOpenSMILES (smiles parity n) = .ok (raw parity n) :=
  parseOpenSMILES_eq_ok_of _ _ _ (actual_syntax_valid parity n)
    (actual_parse_trace parity n) (actual_finalized parity n)
    (raw_parser_introduction_valid parity n)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
