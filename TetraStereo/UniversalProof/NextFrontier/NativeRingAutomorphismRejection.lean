import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeAtoms
import TetraStereo.UniversalProof.NextFrontier.NativeRingCycleGuard
import TetraStereo.OneCenter.ConstitutionAutomorphismSemantics

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingAutomorphismRejection

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingReachability
open TetraStereo.UniversalProof.NativeRingCycleGuard
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-- Every initially unmapped atom eventually receives an atom-compatible image, with its bond
class to each seed pair preserved. This needs only the actual search extension trace. -/
theorem extension_remaining_image {raw : RawMolecule} {edges : List (Nat × Nat)}
    {vertices remaining : List Nat} {mapping finalMapping : List (Nat × Nat)}
    (extension : raw.ConstitutionExtension edges vertices remaining mapping finalMapping)
    (atom : Nat) (member : atom ∈ remaining) (left right : Nat)
    (seeded : (left, right) ∈ mapping) :
    ∃ target, raw.sameConstitutionAtom atom target = true ∧
      raw.constitutionBondClass edges atom left = raw.constitutionBondClass edges target right := by
  induction extension with
  | nil => cases member
  | @step remaining mapping finalMapping chosen target chosenMember candidate tail ih =>
      by_cases same : atom = chosen
      · subst atom
        exact ⟨target, candidate.2.2.1, candidate.2.2.2 (left, right) seeded⟩
      · exact ih ((List.mem_erase_of_ne same).mpr member) (List.mem_cons_of_mem _ seeded)

/-- A uniquely labeled atom distinguishes two seeded roots whenever their bond classes to that
atom differ. The executable exhaustive search itself supplies the extension trace. -/
theorem swap_false_of_unique_atom (raw : RawMolecule) (center left right witness : Nat)
    (different : left ≠ right)
    (unique : ∀ target, raw.sameConstitutionAtom witness target = true → target = witness)
    (reached : witness ∈ raw.reachableAvoiding (raw.atomCount + 1) raw.atomCount [center] [center])
    (notCenter : witness ≠ center) (notLeft : witness ≠ left)
    (distinguished : ∀ edges, raw.constitutionBondClass edges witness left ≠
      raw.constitutionBondClass edges witness right) :
    raw.hasConstitutionAutomorphismSwapping center left right = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  simp only [hasConstitutionAutomorphismSwapping,
    beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte] at accepted
  split at accepted
  · cases accepted
  · have search : raw.searchConstitutionAutomorphismExactAux raw.localizedMancudeEdges
        (raw.reachableAvoiding (raw.atomCount + 1) raw.atomCount [center] [center])
        (((raw.reachableAvoiding (raw.atomCount + 1) raw.atomCount [center] [center]).erase center).erase left).length
        (((raw.reachableAvoiding (raw.atomCount + 1) raw.atomCount [center] [center]).erase center).erase left)
        [(left, right), (center, center)] = true := accepted
    obtain ⟨finalMapping, extension⟩ := raw.searchConstitutionAutomorphismExactAux_sound
      raw.localizedMancudeEdges _ rfl search
    have remaining : witness ∈
        (((raw.reachableAvoiding (raw.atomCount + 1) raw.atomCount [center] [center]).erase center).erase left) :=
      (List.mem_erase_of_ne notLeft).mpr ((List.mem_erase_of_ne notCenter).mpr reached)
    obtain ⟨target, compatible, preserved⟩ := extension_remaining_image extension witness remaining
      left right (by simp)
    rw [unique target compatible] at preserved
    exact distinguished _ preserved

theorem raw_only_chlorine (n : Nat) (parity : TetrahedralInputParity)
    (atom : Nat) (spec : AtomSpec) (observed : (ringRaw n parity).atomAt? atom = some spec)
    (chlorine : spec.element = .Cl) : atom = 3 := by
  by_cases small : atom < 4
  · interval_cases atom <;> simp [ringRaw, atomAt?, listGet?] at observed
    all_goals subst spec
    all_goals simp_all [carbon, taggedCarbon, AtomSpec.aliphatic]
  · have bounded := listGet?_eq_some_implies_lt (ringRaw n parity).atoms atom spec observed
    change atom < (ringRaw n parity).atomCount at bounded
    rw [atom_count] at bounded
    obtain ⟨k, position⟩ : ∃ k, atom = k + 4 := ⟨atom - 4, by omega⟩
    rw [position, ringRaw_atomAt_chain n parity k (by omega)] at observed
    injection observed with equal
    subst spec
    cases chlorine

theorem expanded_only_chlorine (n : Nat) (parity : TetrahedralInputParity)
    (atom : Nat) (spec : AtomSpec) (observed : (expanded n parity).atomAt? atom = some spec)
    (chlorine : spec.element = .Cl) : atom = 3 := by
  by_cases original : atom < (ringRaw n parity).atomCount
  · obtain ⟨sourceSpec, sourceObserved⟩ := listGet?_exists_of_lt (ringRaw n parity).atoms atom original
    have transported := expanded_original_atom n parity atom sourceSpec sourceObserved
    have equal := Option.some.inj (transported.symm.trans observed)
    subst spec
    exact raw_only_chlorine n parity atom sourceSpec sourceObserved chlorine
  · have lower : n + 5 ≤ atom := by rw [atom_count] at original; omega
    have identity := (expanded_fresh_atom n parity atom spec lower observed).1
    subst spec
    cases chlorine

theorem chlorine_fixed_by_compatibility (n : Nat) (parity : TetrahedralInputParity)
    (target : Nat) (compatible : (expanded n parity).sameConstitutionAtom 3 target = true) :
    target = 3 := by
  have chlorine := expanded_original_atom n parity 3 _ (ringRaw_atomAt_three n parity)
  unfold sameConstitutionAtom at compatible
  rw [chlorine] at compatible
  cases targetObserved : (expanded n parity).atomAt? target with
  | none => simp [targetObserved] at compatible
  | some spec =>
      rw [targetObserved] at compatible
      have sameElement : spec.element = .Cl := by
        simp only [Bool.and_eq_true, beq_iff_eq] at compatible
        exact compatible.1.1.1.1.symm
      exact expanded_only_chlorine n parity target spec targetObserved sameElement

theorem chlorine_reached (n : Nat) (parity : TetrahedralInputParity) :
    3 ∈ (expanded n parity).reachableAvoiding ((expanded n parity).atomCount + 1)
      (expanded n parity).atomCount [0] [0] := by
  have path : AvoidingWalk (expanded n parity) (expanded n parity).atomCount 2 0 3 := by
    apply AvoidingWalk.cons
      (avoiding_forward _ _ 0 2 .single (original_edge_retained n parity _ (prefix1_mem n))
        (by rw [expanded_atom_count]; omega))
    exact AvoidingWalk.cons
      (avoiding_forward _ _ 2 3 .single (original_edge_retained n parity _ (prefix2_mem n))
        (by rw [expanded_atom_count]; omega)) (AvoidingWalk.nil 3)
  exact List.contains_iff_mem.mp (reachable_singleton_of_walk _ _ _ 2 0 3 path
    (by rw [expanded_atom_count]; omega))

theorem chlorine_right_bond_zero (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).bondOrder 3 (n + 4) = 0 := by
  rw [bondOrder_symm]
  apply Nat.eq_zero_of_not_pos
  intro positive
  have member := (recordNeighbor_positive_iff _
    (expanded_stereochemical_admissible n parity).1.1 (n + 4) 3).mpr positive
  have listed := (expanded_right_records n parity).mem_iff.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with previous | firstH | secondH | root
  · split at previous <;> omega
  · omega
  · omega
  · omega

theorem chlorine_left_bond_one (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).bondOrder 3 2 = 1 := by
  apply expanded_record_bond_one n parity
  apply List.mem_filterMap.mpr
  exact ⟨⟨2, 3, .single⟩, original_edge_retained n parity _ (prefix2_mem n), rfl⟩

theorem chlorine_bond_classes_differ (n : Nat) (parity : TetrahedralInputParity)
    (edges : List (Nat × Nat)) :
    (expanded n parity).constitutionBondClass edges 3 2 ≠
      (expanded n parity).constitutionBondClass edges 3 (n + 4) := by
  simp only [constitutionBondClass, chlorine_left_bond_one, chlorine_right_bond_zero,
    beq_iff_eq, Nat.one_ne_zero, ↓reduceIte]
  split <;> decide

/-- No successful exact constitutional automorphism can exchange the two carbon arms. The
unique chlorine supplies the contradiction, independently of ring size and search enumeration. -/
theorem actual_no_carbon_swap (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).hasConstitutionAutomorphismSwapping 0 2 (n + 4) = false ∧
    (expanded n parity).hasConstitutionAutomorphismSwapping 0 (n + 4) 2 = false := by
  constructor
  · exact swap_false_of_unique_atom _ 0 2 (n + 4) 3 (by omega)
      (chlorine_fixed_by_compatibility n parity) (chlorine_reached n parity)
      (by decide) (by decide) (chlorine_bond_classes_differ n parity)
  · exact swap_false_of_unique_atom _ 0 (n + 4) 2 3 (by omega)
      (chlorine_fixed_by_compatibility n parity) (chlorine_reached n parity)
      (by decide) (by omega) (fun edges => (chlorine_bond_classes_differ n parity edges).symm)

end TetraStereo.UniversalProof.NativeRingAutomorphismRejection
