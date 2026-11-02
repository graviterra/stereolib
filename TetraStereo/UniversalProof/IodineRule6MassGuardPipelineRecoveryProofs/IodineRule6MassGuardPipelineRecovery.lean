import TetraStereo.UniversalProof.MassEquivalentRule6SymmetryGuardProofs.MassEquivalentRule6SymmetryGuard
import TetraStereo.OneCenter.CIPAuthoritativeRule6SourceTopologySemantics

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.IodineRule6MassGuardPipelineRecoveryProofs.IodineRule6MassGuardPipelineRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
open TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness.DescriptorBranchingRule6CIPFrame
open TetraStereo.UniversalProof.MassEquivalentRule6SymmetryGuardProofs.MassEquivalentRule6SymmetryGuard
open TetraStereo.UniversalProof.MassEquivalentRule6SymmetryGuardProofs.MassEquivalentRule6SymmetryGuard.IodineCounterexample
  (iodineSource ligandAtom sourceCenter ligandSwap positionSwap)















def molecule : RawMolecule where
  atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .I,
    { AtomSpec.aliphatic .I with isotope? := some 127, explicitHydrogens? := some 0 },
    AtomSpec.aliphatic .Br, AtomSpec.aliphatic .F]
  bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]

theorem actual_conversion : molecule.toSemanticMolecule? = some iodineSource.molecule := by
  decide +kernel

theorem actual_unannotated : ∀ atom ∈ molecule.atoms, atom.tetrahedral? = none := by decide +kernel

theorem actual_admissible : molecule.Admissible :=
  molecule.admissible?_eq_true_iff.mp (by decide +kernel)

theorem actual_valence : molecule.ValenceOK := molecule.valenceOK?_eq_true_iff.mp (by decide +kernel)

theorem actual_known_masses : iodineSource.molecule.AllRule2MassesKnown :=
  iodineSource.molecule.allRule2MassesKnown?_eq_true_iff.mp (by decide +kernel)

abbrev ligands : List Nat := molecule.ligandsWithLonePair 0
abbrev roots : List CanonicalRerootCursor := authoritativeSourceRule6LigandCursors molecule 0

def ligandCursor (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

theorem actual_ligands : ligands = [1, 2, 3, 4] := by decide +kernel

theorem actual_roots : roots = [ligandCursor 1, ligandCursor 2, ligandCursor 3, ligandCursor 4] := by
  decide +kernel

theorem actual_roots_length : roots.length = 4 := by decide +kernel

theorem actual_tree : collectCanonicalTreeAuthoritative molecule 2 [canonicalCenterRoot 0] =
    some [canonicalCenterRoot 0, canonicalRoot 0 1, canonicalRoot 0 2,
      canonicalRoot 0 3, canonicalRoot 0 4] := by decide +kernel

theorem actual_auxiliary_state : buildOccurrenceAuxStateFullyAuthoritative? molecule 2 0 = some [] := by
  unfold buildOccurrenceAuxStateFullyAuthoritative?
  rw [actual_tree]
  decide +kernel

def atomicNumbers : List Nat := [53, 53, 35, 9]

theorem actual_initial_table (left right : Fin 4) :
    compareAuthoritativeRule6InitialPositions? molecule [] 2 roots left.val right.val =
      some ({ ordering := compare (atomicNumbers.getD left.val 0) (atomicNumbers.getD right.val 0) } : OccurrenceComparison) := by
  decide +revert +kernel

theorem actual_iodine_tie : compareAuthoritativeRule6InitialPositions? molecule [] 2 roots 0 1 =
    some ({ ordering := .eq } : OccurrenceComparison) := actual_initial_table 0 1

theorem actual_initial_sort :
    sortAuthoritativeRule6InitialPositions? molecule [] 2 roots (List.range 4) = some [0, 1, 2, 3] := by
  decide +kernel

theorem actual_adjacent : compareAuthoritativeRule6InitialAdjacent? molecule [] 2 roots [0, 1, 2, 3] =
    some [some .eq, some .gt, some .gt] := by decide +kernel

def actualPartition (left right : Nat) : Bool :=
  (compareAuthoritativeRule6InitialPositions? molecule [] 2 roots left right).any
    fun decision => decision.ordering = Ordering.eq

/-- The old full-atom identity guard cannot swap ordinary iodine with the distinct isotope record. -/
theorem actual_old_source_guard :
    hasOddConstitutionAutomorphismAtCenter molecule 0 ligands actualPartition = some false := by
  apply (hasOddConstitutionAutomorphismAtCenter_eq_some_false_iff molecule 0 ligands
    actualPartition (by rw [actual_ligands]; rfl)
      (by rw [actual_ligands]; decide)).mpr
  rintro ⟨permutation, member, odd, _, mapping, bijection, seeded⟩
  have seedAtoms : (oddConstitutionSeed 0 ligands permutation).all
      (fun pair => molecule.sameConstitutionAtom pair.1 pair.2) = true := by
    apply List.all_eq_true.mpr
    intro pair retained
    exact bijection.atom_preserving pair (seeded pair retained)
  have member' : permutation ∈ (List.range 4).permutations' :=
    List.mem_permutations'.mpr (List.mem_permutations.mp member)
  -- Only the finite seed label check is evaluated; no exact graph backtracker is reduced.
  have rejected : ((List.range 4).permutations').all (fun candidate =>
      RawMolecule.permutationIsEven candidate ||
        !((oddConstitutionSeed 0 ligands candidate).all
          (fun pair => molecule.sameConstitutionAtom pair.1 pair.2))) = true := by
    decide +kernel
  have impossible := List.all_eq_true.mp rejected permutation member'
  simp only [odd, seedAtoms, Bool.not_true, Bool.false_or] at impossible
  contradiction

/-- A raw runtime frame refinement of93's representation guard. Returned real root nodes and their
previous center are included explicitly; the endpoint map cannot detach the guard from the frame. -/
def RuntimeOddRepresentationGuard (source : AuthoritativeChemicalInput) (mol : RawMolecule)
    (center : source.AromaticCanonicalAtom) (state : OccurrenceAuxState) (fuel : Nat)
    (returnedRoots : List CanonicalRerootCursor) (four : returnedRoots.length = 4) : Prop :=
  ∃ endpoints : Fin 4 → source.AromaticCanonicalAtom,
    Function.Injective endpoints ∧
    (∀ position,
      returnedRoots.get ⟨position.val, by omega⟩ =
        { node := canonicalRoot center.val (endpoints position).val,
          previous? := some (canonicalCenterRoot center.val) }) ∧
    ∃ slots : Equiv.Perm (Fin 4),
      Equiv.Perm.sign slots = -1 ∧
      (∀ position, (compareAuthoritativeRule6InitialPositions? mol state fuel returnedRoots
        position.val (slots position).val).any (fun result => result.ordering = .eq) = true) ∧
      ∃ atoms : Equiv.Perm source.AromaticCanonicalAtom,
        AromaticCanonicalConstitutionRepresentationAutomorphism source atoms ∧
        atoms center = center ∧
        ∀ position, atoms (endpoints position) = endpoints (slots position)

theorem actual_returned_root_binding (position : Fin 4) :
    roots.get ⟨position.val, by rw [actual_roots_length]; exact position.isLt⟩ =
      ({ node := canonicalRoot sourceCenter.val (ligandAtom position).val,
         previous? := some (canonicalCenterRoot sourceCenter.val) } : CanonicalRerootCursor) := by
  fin_cases position <;> decide +kernel

theorem actual_partition_swap_preserved (position : Fin 4) :
    (compareAuthoritativeRule6InitialPositions? molecule [] 2 roots position.val
      (positionSwap position).val).any (fun result => result.ordering = .eq) = true := by
  fin_cases position <;> decide +kernel

theorem actual_representation_guard :
    RuntimeOddRepresentationGuard iodineSource molecule sourceCenter [] 2 roots actual_roots_length := by
  refine ⟨ligandAtom, IodineCounterexample.ligandAtom_injective, actual_returned_root_binding,
    positionSwap, IodineCounterexample.positionSwap_odd, actual_partition_swap_preserved,
    ligandSwap, IodineCounterexample.ligandSwap_representation_automorphism,
    IodineCounterexample.ligandSwap_zero, IodineCounterexample.ligandSwap_transports_ligand_atoms⟩

/-- Exact semantic guard status, requiring known masses before interpreting either polarity. -/
noncomputable def representationGuard? (source : AuthoritativeChemicalInput) (mol : RawMolecule)
    (center : source.AromaticCanonicalAtom) (state : OccurrenceAuxState) (fuel : Nat)
    (returnedRoots : List CanonicalRerootCursor) (four : returnedRoots.length = 4) : Option Bool := by
  classical
  exact if source.molecule.AllRule2MassesKnown then
    some (decide (RuntimeOddRepresentationGuard source mol center state fuel returnedRoots four))
  else none

theorem representationGuard?_eq_some_true_iff (source : AuthoritativeChemicalInput) (mol : RawMolecule)
    (center : source.AromaticCanonicalAtom) (state : OccurrenceAuxState) (fuel : Nat)
    (returnedRoots : List CanonicalRerootCursor) (four : returnedRoots.length = 4) :
    representationGuard? source mol center state fuel returnedRoots four = some true ↔
      source.molecule.AllRule2MassesKnown ∧
        RuntimeOddRepresentationGuard source mol center state fuel returnedRoots four := by
  classical
  by_cases known : source.molecule.AllRule2MassesKnown <;> simp [representationGuard?, known]

theorem actual_new_guard : representationGuard? iodineSource molecule sourceCenter [] 2 roots
    actual_roots_length = some true :=
  (representationGuard?_eq_some_true_iff _ _ _ _ _ _ _).mpr
    ⟨actual_known_masses, actual_representation_guard⟩

/-- NEW source adapter with the same actual auxiliary/initial-sort/adjacent stages. Its source
molecule must be the actual raw conversion; the old production API is unchanged. -/
noncomputable def representationSourceStereogenicity? (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (_conversion : mol.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalAtom) (fuel : Nat) : Option Bool := by
  classical
  let returnedRoots := authoritativeSourceRule6LigandCursors mol center.val
  exact if four : returnedRoots.length = 4 then do
    let state ← buildOccurrenceAuxStateFullyAuthoritative? mol fuel center.val
    let sorted ← sortAuthoritativeRule6InitialPositions? mol state fuel returnedRoots (List.range 4)
    let adjacent ← compareAuthoritativeRule6InitialAdjacent? mol state fuel returnedRoots sorted
    if some Ordering.lt ∈ adjacent then none else
      match representationGuard? source mol center state fuel returnedRoots four with
      | none => none
      | some true => some false
      | some false => (authoritativeResolvedRule6Stereogenicity? mol state fuel
          (canonicalCenterRoot center.val) returnedRoots sorted adjacent)
  else some false

noncomputable def representationSourceOutcome? (source : AuthoritativeChemicalInput) (mol : RawMolecule)
    (conversion : mol.toSemanticMolecule? = some source.molecule)
    (center : source.AromaticCanonicalAtom) (fuel : Nat) : Option StereoOutcome :=
  match representationSourceStereogenicity? source mol conversion center fuel with
  | some true => some (.refused .notSpecified)
  | some false => none
  | none => some (.refused .rankingUnresolved)

theorem actual_new_source_not_stereogenic :
    representationSourceStereogenicity? iodineSource molecule actual_conversion sourceCenter 2 =
      some false := by
  simp [representationSourceStereogenicity?, sourceCenter,
    actual_auxiliary_state, actual_initial_sort, actual_adjacent]
  intro four
  have guard : representationGuard? iodineSource molecule sourceCenter [] 2 roots four = some true :=
    actual_new_guard
  change (match representationGuard? iodineSource molecule sourceCenter [] 2 roots four with
    | none => none
    | some true => some false
    | some false => authoritativeResolvedRule6Stereogenicity? molecule [] 2 (canonicalCenterRoot 0) roots [0, 1, 2, 3] [some .eq, some .gt, some .gt]) = some false
  rw [guard]

theorem actual_new_source_outcome_none :
    representationSourceOutcome? iodineSource molecule actual_conversion sourceCenter 2 = none := by
  simp [representationSourceOutcome?, actual_new_source_not_stereogenic]

theorem actual_guard_difference :
    hasOddConstitutionAutomorphismAtCenter molecule 0 ligands actualPartition = some false ∧
      representationGuard? iodineSource molecule sourceCenter [] 2 roots actual_roots_length = some true :=
  ⟨actual_old_source_guard, actual_new_guard⟩

end TetraStereo.UniversalProof.IodineRule6MassGuardPipelineRecoveryProofs.IodineRule6MassGuardPipelineRecovery
