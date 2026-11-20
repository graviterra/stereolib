import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-!
A finite propagation certificate for the actual 46-atom input graph. Fixing the shortcut
history and the inherited reference forces all atoms fixed. Each of the 31 new atoms is
identified by atomic number, isotope mass, bond orders to already fixed atoms, and
injectivity excluding those atoms. The finite uniqueness checks use the actual graph.
No enumeration of permutations, evaluator outcomes or desired label equality is used.

The source certificate is `s3-cfi-shortcut-fixing-certificate.json`, SHA256
`5aec2b76a9b9ba272d290e2257d87e538330d4bec41368b6fefb1c5a61650da8`. Indices use the compact mapping documented in ReferenceOrbitInput.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer

open LocalizedChemicalRingReferenceOrbitInput

section General
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A new atom's color and adjacency signature isolates it among the atoms not yet fixed. -/
def SignatureUnique (m : MoleculeGraph V) (pins : List V) (a : V) : Prop :=
  ∀ candidate, candidate ∉ pins → m.atomZ candidate = m.atomZ a →
    m.atomMass candidate = m.atomMass a →
    (∀ p ∈ pins, m.bond candidate p = m.bond a p) → candidate = a

/-- Graph preservation plus injectivity turn a checked signature into one more fixed atom. -/
theorem fixed_of_signature (m : MoleculeGraph V) (e : m.Aut) (pins : List V) (a : V)
    (fixed : ∀ p ∈ pins, (e : Equiv.Perm V) p = p)
    (unique : SignatureUnique m pins a) : (e : Equiv.Perm V) a = a := by
  classical
  by_cases present : a ∈ pins
  · exact fixed a present
  · apply unique ((e : Equiv.Perm V) a)
    · intro inPins
      have impossible := (e : Equiv.Perm V).injective (fixed _ inPins)
      exact present (impossible ▸ inPins)
    · exact MoleculeGraph.Aut.atomZ_eq (m := m) e a
    · exact MoleculeGraph.Aut.atomMass_eq (m := m) e a
    · intro p member
      have eq := MoleculeGraph.Aut.bond_eq (m := m) e a p
      rw [fixed p member] at eq
      exact eq

private theorem extend_fixed (m : MoleculeGraph V) (e : m.Aut) (pins : List V) (a : V)
    (fixed : ∀ p ∈ pins, (e : Equiv.Perm V) p = p)
    (unique : SignatureUnique m pins a) : ∀ p ∈ a :: pins, (e : Equiv.Perm V) p = p := by
  intro p member
  rcases List.mem_cons.mp member with same | before
  · subst p
    exact fixed_of_signature m e pins a fixed unique
  · exact fixed p before

end General

private def pins0 : List (Fin 46) := [0, 28, 32, 27, 26, 34, 38, 42, 40, 3, 14, 8, 5, 2, 30]
private def pins1 : List (Fin 46) := 1 :: pins0
private def pins2 : List (Fin 46) := 4 :: pins1
private def pins3 : List (Fin 46) := 11 :: pins2
private def pins4 : List (Fin 46) := 15 :: pins3
private def pins5 : List (Fin 46) := 20 :: pins4
private def pins6 : List (Fin 46) := 21 :: pins5
private def pins7 : List (Fin 46) := 29 :: pins6
private def pins8 : List (Fin 46) := 31 :: pins7
private def pins9 : List (Fin 46) := 33 :: pins8
private def pins10 : List (Fin 46) := 35 :: pins9
private def pins11 : List (Fin 46) := 36 :: pins10
private def pins12 : List (Fin 46) := 37 :: pins11
private def pins13 : List (Fin 46) := 39 :: pins12
private def pins14 : List (Fin 46) := 43 :: pins13
private def pins15 : List (Fin 46) := 44 :: pins14
private def pins16 : List (Fin 46) := 45 :: pins15
private def pins17 : List (Fin 46) := 12 :: pins16
private def pins18 : List (Fin 46) := 13 :: pins17
private def pins19 : List (Fin 46) := 23 :: pins18
private def pins20 : List (Fin 46) := 25 :: pins19
private def pins21 : List (Fin 46) := 41 :: pins20
private def pins22 : List (Fin 46) := 6 :: pins21
private def pins23 : List (Fin 46) := 7 :: pins22
private def pins24 : List (Fin 46) := 9 :: pins23
private def pins25 : List (Fin 46) := 10 :: pins24
private def pins26 : List (Fin 46) := 16 :: pins25
private def pins27 : List (Fin 46) := 17 :: pins26
private def pins28 : List (Fin 46) := 18 :: pins27
private def pins29 : List (Fin 46) := 19 :: pins28
private def pins30 : List (Fin 46) := 22 :: pins29
private def pins31 : List (Fin 46) := 24 :: pins30

private theorem unique0 : SignatureUnique graph pins0 (1 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique1 : SignatureUnique graph pins1 (4 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique2 : SignatureUnique graph pins2 (11 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique3 : SignatureUnique graph pins3 (15 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique4 : SignatureUnique graph pins4 (20 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique5 : SignatureUnique graph pins5 (21 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique6 : SignatureUnique graph pins6 (29 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique7 : SignatureUnique graph pins7 (31 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique8 : SignatureUnique graph pins8 (33 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique9 : SignatureUnique graph pins9 (35 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique10 : SignatureUnique graph pins10 (36 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique11 : SignatureUnique graph pins11 (37 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique12 : SignatureUnique graph pins12 (39 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique13 : SignatureUnique graph pins13 (43 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique14 : SignatureUnique graph pins14 (44 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique15 : SignatureUnique graph pins15 (45 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique16 : SignatureUnique graph pins16 (12 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique17 : SignatureUnique graph pins17 (13 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique18 : SignatureUnique graph pins18 (23 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique19 : SignatureUnique graph pins19 (25 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique20 : SignatureUnique graph pins20 (41 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique21 : SignatureUnique graph pins21 (6 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique22 : SignatureUnique graph pins22 (7 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique23 : SignatureUnique graph pins23 (9 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique24 : SignatureUnique graph pins24 (10 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique25 : SignatureUnique graph pins25 (16 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique26 : SignatureUnique graph pins26 (17 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique27 : SignatureUnique graph pins27 (18 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique28 : SignatureUnique graph pins28 (19 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique29 : SignatureUnique graph pins29 (22 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel
private theorem unique30 : SignatureUnique graph pins30 (24 : Fin 46) := by
  unfold SignatureUnique
  decide +kernel

/-- Every constitutional automorphism fixing the actual shortcut and inherited mark is identity. -/
theorem shortcut_stabilizer (e : graph.Aut)
    (historyFixed : ∀ a ∈ shortcutPath, (e : Equiv.Perm (Fin 46)) a = a)
    (referenceFixed : (e : Equiv.Perm (Fin 46)) reference = reference) :
    (e : Equiv.Perm (Fin 46)) = 1 := by
  have seed : ∀ a ∈ pins0, (e : Equiv.Perm (Fin 46)) a = a := by
    intro a member
    have listEq : pins0 = shortcutPath ++ [reference] := rfl
    rw [listEq] at member
    rcases List.mem_append.mp member with path | mark
    · exact historyFixed a path
    · have same : a = reference := List.mem_singleton.mp mark
      simpa only [same] using referenceFixed
  have fixed1 := extend_fixed graph e pins0 (1 : Fin 46) seed unique0
  have fixed2 := extend_fixed graph e pins1 (4 : Fin 46) fixed1 unique1
  have fixed3 := extend_fixed graph e pins2 (11 : Fin 46) fixed2 unique2
  have fixed4 := extend_fixed graph e pins3 (15 : Fin 46) fixed3 unique3
  have fixed5 := extend_fixed graph e pins4 (20 : Fin 46) fixed4 unique4
  have fixed6 := extend_fixed graph e pins5 (21 : Fin 46) fixed5 unique5
  have fixed7 := extend_fixed graph e pins6 (29 : Fin 46) fixed6 unique6
  have fixed8 := extend_fixed graph e pins7 (31 : Fin 46) fixed7 unique7
  have fixed9 := extend_fixed graph e pins8 (33 : Fin 46) fixed8 unique8
  have fixed10 := extend_fixed graph e pins9 (35 : Fin 46) fixed9 unique9
  have fixed11 := extend_fixed graph e pins10 (36 : Fin 46) fixed10 unique10
  have fixed12 := extend_fixed graph e pins11 (37 : Fin 46) fixed11 unique11
  have fixed13 := extend_fixed graph e pins12 (39 : Fin 46) fixed12 unique12
  have fixed14 := extend_fixed graph e pins13 (43 : Fin 46) fixed13 unique13
  have fixed15 := extend_fixed graph e pins14 (44 : Fin 46) fixed14 unique14
  have fixed16 := extend_fixed graph e pins15 (45 : Fin 46) fixed15 unique15
  have fixed17 := extend_fixed graph e pins16 (12 : Fin 46) fixed16 unique16
  have fixed18 := extend_fixed graph e pins17 (13 : Fin 46) fixed17 unique17
  have fixed19 := extend_fixed graph e pins18 (23 : Fin 46) fixed18 unique18
  have fixed20 := extend_fixed graph e pins19 (25 : Fin 46) fixed19 unique19
  have fixed21 := extend_fixed graph e pins20 (41 : Fin 46) fixed20 unique20
  have fixed22 := extend_fixed graph e pins21 (6 : Fin 46) fixed21 unique21
  have fixed23 := extend_fixed graph e pins22 (7 : Fin 46) fixed22 unique22
  have fixed24 := extend_fixed graph e pins23 (9 : Fin 46) fixed23 unique23
  have fixed25 := extend_fixed graph e pins24 (10 : Fin 46) fixed24 unique24
  have fixed26 := extend_fixed graph e pins25 (16 : Fin 46) fixed25 unique25
  have fixed27 := extend_fixed graph e pins26 (17 : Fin 46) fixed26 unique26
  have fixed28 := extend_fixed graph e pins27 (18 : Fin 46) fixed27 unique27
  have fixed29 := extend_fixed graph e pins28 (19 : Fin 46) fixed28 unique28
  have fixed30 := extend_fixed graph e pins29 (22 : Fin 46) fixed29 unique29
  have fixed31 := extend_fixed graph e pins30 (24 : Fin 46) fixed30 unique30
  apply Equiv.ext
  intro a
  have coverage : ∀ v : Fin 46, v ∈ pins31 := by decide +kernel
  exact fixed31 a (coverage a)

/-- The detected-center automorphism has the same atom action, so the same finite
certificate proves its triviality without a supplied physical-sign premise. -/
theorem detected_shortcut_stabilizer (e : physical.Aut)
    (historyFixed : ∀ a ∈ shortcutPath, e.val a = a)
    (referenceFixed : e.val reference = reference) : e = 1 := by
  apply Subtype.ext
  exact shortcut_stabilizer ⟨e.val, e.2.1⟩ historyFixed referenceFixed

/-- The exact raw-history formulation consumed by the actual evaluator's rigidity
theorem. The finite atom pins are derived from this reached node's stored history. -/
theorem raw_shortcut_stabilizer (e : physical.Aut)
    (historyFixed : ∀ value ∈ shortcutNode.history,
      LocalizedChemicalRingPhysicalSense.relabelOf certified
        e.val value = value)
    (referenceFixed : e.val reference = reference) : e = 1 := by
  apply detected_shortcut_stabilizer e _ referenceFixed
  intro a present
  have inHistory : a.val ∈ shortcutNode.history := by
    change a.val ∈ (shortcutPath.map Fin.val).reverse
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨a, present, rfl⟩)
  have fixed := historyFixed a.val inHistory
  rw [LocalizedChemicalRingPhysicalSense.relabelOf_val] at fixed
  exact Fin.ext fixed

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer.fixed_of_signature
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer.shortcut_stabilizer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer.detected_shortcut_stabilizer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer.raw_shortcut_stabilizer
