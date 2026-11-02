import TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Molecular local configurations determine the recursive report

On a well-formed finite single-bond raw molecule with unique bond records, the handedness of
each degree-four molecular neighborhood determines every recursively generated auxiliary fact
and the experimental emitted report. Occurrence histories, auxiliary labels, winning references
and comparison outcomes are not configuration premises. The phantom has no physical coordinate;
three-neighbor lone-pair frames therefore refuse in this physical-atom geometry model.

The graph and atom identities remain fixed. This is dependence on physical local configurations,
not independent chemical priority, successful report coverage, or a cross-molecule theorem.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration

open LocalizedGenericMarkedRecalculation LocalizedMarkedConfigurationTransport
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors

private theorem map_idxOf_eq_range (atoms : List Nat) (nodup : atoms.Nodup) :
    atoms.map atoms.idxOf = List.range atoms.length := by
  calc
    atoms.map atoms.idxOf = ((List.finRange atoms.length).map
        (fun i : Fin atoms.length => atoms[i.val])).map atoms.idxOf := by
      rw [List.map_getElem_finRange]
    _ = List.range atoms.length := by
      simp only [List.map_map, Function.comp_def, nodup.idxOf_getElem,
        List.map_coe_finRange_eq_range]

private theorem select_idxOf (base : List Nat) (atoms : List Nat)
    (inside : ∀ atom ∈ atoms, atom ∈ base) :
    atomsAt? base (atoms.map base.idxOf) = some atoms := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      have head := List.getElem?_idxOf (inside atom (by simp))
      have rest := ih (fun x hx => inside x (List.mem_cons_of_mem atom hx))
      simp only [atomsAt?, List.map_cons, List.mapM_cons, head]
      change (atomsAt? base (tail.map base.idxOf)).bind (fun rest => some (atom :: rest)) = _
      rw [rest]
      rfl

/-- Agreement on one ordered neighborhood transports to any permutation of its four atoms. -/
theorem readback_perm_congr {first second : Geometry} (base atoms : List Nat)
    (nodup : base.Nodup) (four : base.length = 4) (permutation : atoms.Perm base)
    (agree : readback? first base = readback? second base) :
    readback? first atoms = readback? second atoms := by
  let positions := atoms.map base.idxOf
  have indices : positions.Perm [0, 1, 2, 3] := by
    have mapped := permutation.map base.idxOf
    rw [map_idxOf_eq_range base nodup, four] at mapped
    exact mapped
  have selected := select_idxOf base atoms (fun _ member => permutation.mem_iff.mp member)
  rcases base with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩ <;> simp at four
  subst tail
  have expand (geom : Geometry) :
      (atomsAt? [a, b, c, d] positions).bind (readback? geom) =
        if RawMolecule.permutationIsEven positions then readback? geom [a, b, c, d]
        else (readback? geom [a, b, c, d]).map RS.swap := by
    simpa using reordered_readback_partial geom ![a, b, c, d] positions indices
  have eq : (atomsAt? [a, b, c, d] positions).bind (readback? first) =
      (atomsAt? [a, b, c, d] positions).bind (readback? second) := by
    rw [expand first, expand second, agree]
  simpa [positions, selected] using eq

/-- One signed geometric reading at every degree-four atom, in molecular bond-list order. -/
def SameMolecularConfigurations (mol : RawMolecule) (first second : Geometry) : Prop :=
  ∀ atom, atom < mol.atomCount → (mol.canonicalIncidentNeighbors atom).length = 4 →
    readback? first (mol.canonicalIncidentNeighbors atom) =
      readback? second (mol.canonicalIncidentNeighbors atom)

/-- The molecular configuration inventory supplies every reached occurrence-frame condition. -/
theorem reached_configurations (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) {first second : Geometry}
    (firstPhantom : first mol.atomCount = none) (secondPhantom : second mol.atomCount = none)
    (agree : SameMolecularConfigurations mol first second) :
    SameReachedConfigurations mol first second := by
  intro node reached atoms frame
  rcases frame_atoms_perm_neighbors mol wellFormed single node reached atoms frame with
    ⟨four, permutation⟩ | ⟨_, permutation⟩
  · exact readback_perm_congr _ _ (mol.canonicalIncidentNeighbors_nodup node.atom unique) four
      permutation (agree node.atom (reached_atom_valid mol wellFormed node reached) four)
  · have phantom : mol.atomCount ∈ atoms := permutation.mem_iff.mpr (by simp)
    rw [readback_none_of_missing first atoms _ phantom firstPhantom,
      readback_none_of_missing second atoms _ phantom secondPhantom]

/-- All generated auxiliary facts are fixed by degree-four molecular configurations. -/
theorem facts_of_molecular_configurations (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) {first second : Geometry}
    (firstPhantom : first mol.atomCount = none) (secondPhantom : second mol.atomCount = none)
    (agree : SameMolecularConfigurations mol first second) (fuel depth : Nat)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node) (reached : Reached mol node) :
    facts mol fuel depth first state ctx node = facts mol fuel depth second state ctx node :=
  LocalizedMarkedReachableConfigurations.facts_congr mol fuel depth first second
    (reached_configurations mol wellFormed single unique firstPhantom secondPhantom agree)
    state ctx node reached

/-- The actual experimental report depends only on the finite molecular configuration inventory. -/
theorem assign_of_molecular_configurations (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) {first second : Geometry}
    (firstPhantom : first mol.atomCount = none) (secondPhantom : second mol.atomCount = none)
    (agree : SameMolecularConfigurations mol first second) : assign mol first = assign mol second :=
  LocalizedMarkedReachableConfigurations.assign_congr mol
    (reached_configurations mol wellFormed single unique firstPhantom secondPhantom agree)

end TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration.readback_perm_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration.reached_configurations
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration.facts_of_molecular_configurations
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration.assign_of_molecular_configurations
