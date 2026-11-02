/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TetraStereo team
-/

import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization
import TetraStereo.OneCenter.IUPACP94NormalizationReadinessCore
import TetraStereo.OneCenter.P93SourceHydrogenFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000


























































































namespace TetraStereo
namespace OneCenter
namespace P93NormalizationIdempotence

open RawMolecule
open TetraStereo.OneCenter.BlueBookP93.NoncarbonTetrahedra.Production

/-! ## Extensionality for `RawMolecule`

The production structures are ordinary structures, but `rcases`-based record extensionality is
fragile in tactic scripts; this lemma records the four components directly. -/

theorem rawMolecule_ext {left right : RawMolecule}
    (hAtoms : left.atoms = right.atoms)
    (hBonds : left.bonds = right.bonds)
    (hNeighbors : left.neighborOrder = right.neighborOrder)
    (hPredecessors : left.introductionPredecessors = right.introductionPredecessors) :
    left = right := by
  rcases left with ⟨leftAtoms, leftBonds, leftNeighbors, leftPredecessors⟩
  rcases right with ⟨rightAtoms, rightBonds, rightNeighbors, rightPredecessors⟩
  simp only [RawMolecule.mk.injEq]
  exact ⟨hAtoms, hBonds, hNeighbors, hPredecessors⟩

/-! ## Explicit-hydrogen closure

`F` stores `mol.hydrogenCountAt index` in the atom's `explicitHydrogens?` field. On molecules all
of whose atoms already carry some explicit hydrogen policy, this is the identity, and being
"all explicit" is preserved by `F`, `N`, and `U`.

`AllExplicit` is definitionally the core repair's `AllExplicitHydrogens`
(`allExplicit_iff_allExplicitHydrogens`); the local name is retained for downstream modules that
already refer to it. -/

/-- Every atom of the molecule carries an explicit hydrogen policy. This is the structural output
invariant of `freezeSourceHydrogenCounts`. -/
def AllExplicit (mol : RawMolecule) : Prop :=
  ∀ index atom, mol.atomAt? index = some atom → ∃ count, atom.explicitHydrogens? = some count

/-- `AllExplicit` is the core repair's explicit-hydrogen domain, definitionally. -/
theorem allExplicit_iff_allExplicitHydrogens (mol : RawMolecule) :
    AllExplicit mol ↔ AllExplicitHydrogens mol := by
  unfold AllExplicit AllExplicitHydrogens
  rfl

theorem allExplicit_freezeSourceHydrogenCounts (mol : RawMolecule) :
    AllExplicit (freezeSourceHydrogenCounts mol) := by
  intro index atom lookup
  rw [freezeSourceHydrogenCounts_atomAt?] at lookup
  cases sourceLookup : mol.atomAt? index with
  | none => simp [sourceLookup] at lookup
  | some source =>
      simp [sourceLookup] at lookup
      cases lookup
      exact ⟨mol.hydrogenCountAt index, rfl⟩

theorem allExplicit_normalize (mol : RawMolecule) (explicit : AllExplicit mol) :
    AllExplicit (normalize mol) := by
  intro index atom lookup
  rw [normalize_atomAt?] at lookup
  cases sourceLookup : mol.atomAt? index with
  | none => simp [sourceLookup] at lookup
  | some source =>
      simp [sourceLookup] at lookup
      cases lookup
      obtain ⟨count, explicitCount⟩ := explicit index source sourceLookup
      exact ⟨count, by rw [normalizeAtom_explicitHydrogens?]; exact explicitCount⟩

theorem allExplicit_normalizeUnspecifiedBonds (mol : RawMolecule) (explicit : AllExplicit mol) :
    AllExplicit mol.normalizeUnspecifiedBonds := by
  intro index atom lookup
  have lookup' : mol.atomAt? index = some atom := by
    simpa [RawMolecule.normalizeUnspecifiedBonds, RawMolecule.atomAt?] using lookup
  exact explicit index atom lookup'

/-- On a molecule all of whose atoms already carry an explicit hydrogen policy, the freezing
pass is the identity.  This is the core repair's audited theorem, restated under the local name
`AllExplicit`. -/
theorem freezeSourceHydrogenCounts_eq_self_of_allExplicit (mol : RawMolecule)
    (explicit : AllExplicit mol) :
    freezeSourceHydrogenCounts mol = mol :=
  freezeSourceHydrogenCounts_eq_self_of_allExplicitHydrogens mol explicit

/-! ## Idempotence of `U`, the unspecified-bond straightening -/

/-- `normalizeUnspecifiedBonds` rewrites only unresolved bond kinds, so applying it twice is the
same as applying it once. This is derived from the general API of the readiness core rather than
restated for the production pipeline. -/
theorem normalizeUnspecifiedBonds_idempotent (mol : RawMolecule) :
    mol.normalizeUnspecifiedBonds.normalizeUnspecifiedBonds =
      mol.normalizeUnspecifiedBonds :=
  RawMolecule.normalizeUnspecifiedBonds_eq_self_of_resolved _
    (RawMolecule.normalizeUnspecifiedBonds_bondsResolved mol)







theorem effectiveOxoCenter?_normalize (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? (normalize mol) center = effectiveOxoCenter? mol center := by
  unfold effectiveOxoCenter?
  rw [normalize_atomAt?, normalize_writtenNeighbors]
  cases mol.atomAt? center <;> simp [normalizeAtom_explicitHydrogens?]

theorem oxygenAt?_normalize (mol : RawMolecule) (atom : Nat) :
    oxygenAt? (normalize mol) atom = oxygenAt? mol atom := by
  unfold oxygenAt?
  rw [normalize_atomAt?]
  cases mol.atomAt? atom <;> simp

/-- The effective-oxo bond predicate ignores the bond kind, so rewriting that kind cannot change
it. -/
theorem effectiveOxoBond?_normalizeBond (mol : RawMolecule) (bond : RawBond) :
    effectiveOxoBond? (normalize mol) (normalizeBond mol bond) =
      effectiveOxoBond? mol bond := by
  simp only [effectiveOxoBond?, normalizeBond_source, normalizeBond_target,
    effectiveOxoCenter?_normalize, oxygenAt?_normalize]

/-- A bond selected by the effective-oxo predicate is rewritten to `single` by `normalizeBond`. -/
theorem normalizeBond_eq_single_of_effective (mol : RawMolecule) (bond : RawBond)
    (effective : effectiveOxoBond? mol bond = true) :
    normalizeBond mol bond = { bond with kind := ParsedBondKind.single } := by
  simp [normalizeBond, effective]

/-- A bond not selected by the effective-oxo predicate is left unchanged. -/
theorem normalizeBond_eq_self_of_not_effective (mol : RawMolecule) (bond : RawBond)
    (notEffective : effectiveOxoBond? mol bond = false) :
    normalizeBond mol bond = bond := by
  simp [normalizeBond, notEffective]

/-- A selected bond whose kind is already `single` is left unchanged. -/
theorem normalizeBond_eq_self_of_effective_of_kind_eq_single
    (mol : RawMolecule) (bond : RawBond)
    (effective : effectiveOxoBond? mol bond = true)
    (kindEq : bond.kind = ParsedBondKind.single) :
    normalizeBond mol bond = bond := by
  rw [normalizeBond_eq_single_of_effective mol bond effective]
  rcases bond with ⟨source, target, kind⟩
  simp_all

theorem chargeInsensitiveAtom?_normalize (mol : RawMolecule) (index : Nat) :
    chargeInsensitiveAtom? (normalize mol) index =
      chargeInsensitiveAtom? mol index := by
  unfold chargeInsensitiveAtom?
  change
    (mol.bonds.map (normalizeBond mol)).any (fun bond =>
        effectiveOxoBond? (normalize mol) bond &&
          (bond.source == index || bond.target == index)) = _
  rw [List.any_map]
  congr 1
  funext bond
  change
    (effectiveOxoBond? (normalize mol) (normalizeBond mol bond) &&
        ((normalizeBond mol bond).source == index ||
          (normalizeBond mol bond).target == index)) =
      (effectiveOxoBond? mol bond && (bond.source == index || bond.target == index))
  rw [effectiveOxoBond?_normalizeBond, normalizeBond_source, normalizeBond_target]

/-- Because the charge-insensitivity predicate is invariant under `N`, the two rewrites `N` and
`N` composed with itself act identically on a single atom, not merely on already-normalized
atoms. -/
theorem normalizeAtom_normalize_apply (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    normalizeAtom (normalize mol) index atom = normalizeAtom mol index atom := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible, chargeInsensitiveAtom?_normalize]

theorem normalizeAtomsAux_normalize_apply (mol : RawMolecule) (offset : Nat)
    (atoms : List AtomSpec) :
    normalizeAtomsAux (normalize mol) offset atoms =
      normalizeAtomsAux mol offset atoms := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp only [normalizeAtomsAux]
      rw [normalizeAtom_normalize_apply, ih (offset + 1)]

theorem normalizeAtom_normalize (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    normalizeAtom (normalize mol) index (normalizeAtom mol index atom) =
      normalizeAtom mol index atom := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible, chargeInsensitiveAtom?_normalize]

theorem normalizeAtomsAux_normalize (mol : RawMolecule) (offset : Nat)
    (atoms : List AtomSpec) :
    normalizeAtomsAux (normalize mol) offset (normalizeAtomsAux mol offset atoms) =
      normalizeAtomsAux mol offset atoms := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp only [normalizeAtomsAux]
      rw [normalizeAtom_normalize, ih (offset + 1)]

theorem normalizeAtoms_normalize (mol : RawMolecule) :
    normalizeAtoms (normalize mol) = normalizeAtoms mol := by
  show normalizeAtomsAux (normalize mol) 0 (normalizeAtomsAux mol 0 mol.atoms) =
    normalizeAtomsAux mol 0 mol.atoms
  exact normalizeAtomsAux_normalize mol 0 mol.atoms

theorem normalizeBond_normalize (mol : RawMolecule) (bond : RawBond) :
    normalizeBond (normalize mol) (normalizeBond mol bond) =
      normalizeBond mol bond := by
  conv_lhs => rw [normalizeBond]
  rw [effectiveOxoBond?_normalizeBond]
  by_cases effective : effectiveOxoBond? mol bond = true
  · simp [normalizeBond, effective]
  · have notEffective : effectiveOxoBond? mol bond = false := by
      cases observed : effectiveOxoBond? mol bond <;> simp_all
    simp [notEffective]

theorem map_normalizeBond_normalizeBond (mol : RawMolecule) (bonds : List RawBond) :
    (bonds.map (normalizeBond mol)).map (normalizeBond (normalize mol)) =
      bonds.map (normalizeBond mol) := by
  induction bonds with
  | nil => rfl
  | cons bond rest ih =>
      simp only [List.map_cons]
      rw [normalizeBond_normalize, ih]

theorem normalize_bonds_normalize (mol : RawMolecule) :
    (normalize (normalize mol)).bonds = (normalize mol).bonds := by
  show (mol.bonds.map (normalizeBond mol)).map (normalizeBond (normalize mol)) =
    mol.bonds.map (normalizeBond mol)
  exact map_normalizeBond_normalizeBond mol mol.bonds

/-- **The quotient rewrite is idempotent on every molecule.** No structural hypothesis is
needed: the effective-oxo center predicate only inspects elements, the written neighbor
inventory and the stored inline hydrogen policy, and the effective-oxo bond predicate
deliberately ignores bond kinds. -/
theorem normalize_normalize (mol : RawMolecule) :
    normalize (normalize mol) = normalize mol := by
  apply rawMolecule_ext
  · exact normalizeAtoms_normalize mol
  · exact normalize_bonds_normalize mol
  · rfl
  · rfl

/-! ## The bridge `N (U (N m)) = U (N m)`

`U` only resolves `unspecified` bond kinds. Every effective-oxo bond of `N m` has already been
forced to `single` by `N`, and `U` never changes atom data, the stored hydrogen policy, endpoints,
or the written neighbor inventory, so the active-center predicates are unchanged and `N` has
nothing left to do. -/

theorem effectiveOxoCenter?_normalizeUnspecifiedBonds (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? mol.normalizeUnspecifiedBonds center =
      effectiveOxoCenter? mol center := by
  unfold effectiveOxoCenter?
  rw [RawMolecule.normalizeUnspecifiedBonds_writtenNeighbors]
  rfl

theorem oxygenAt?_normalizeUnspecifiedBonds (mol : RawMolecule) (atom : Nat) :
    oxygenAt? mol.normalizeUnspecifiedBonds atom = oxygenAt? mol atom := by
  unfold oxygenAt?
  rfl

/-- Endpoint-only version of the effective-oxo bond predicate, so that a normalizer applied to
the bond can be absorbed while a different molecule is used for the predicates. -/
theorem effectiveOxoBond?_normalizeUnspecifiedBond_any
    (predicateMolecule normalizingMolecule : RawMolecule) (bond : RawBond) :
    effectiveOxoBond? predicateMolecule (normalizingMolecule.normalizeUnspecifiedBond bond) =
      effectiveOxoBond? predicateMolecule bond := by
  unfold effectiveOxoBond?
  rw [RawMolecule.normalizeUnspecifiedBond_source,
    RawMolecule.normalizeUnspecifiedBond_target]

/-- Endpoint-only version for the quotient bond rewrite. -/
theorem effectiveOxoBond?_normalizeBond_any
    (predicateMolecule normalizingMolecule : RawMolecule) (bond : RawBond) :
    effectiveOxoBond? predicateMolecule (normalizeBond normalizingMolecule bond) =
      effectiveOxoBond? predicateMolecule bond := by
  unfold effectiveOxoBond?
  rw [normalizeBond_source, normalizeBond_target]

theorem effectiveOxoCenter?_normalizeUnspecifiedBonds_normalize
    (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? (normalize mol).normalizeUnspecifiedBonds center =
      effectiveOxoCenter? mol center := by
  rw [effectiveOxoCenter?_normalizeUnspecifiedBonds, effectiveOxoCenter?_normalize]

theorem oxygenAt?_normalizeUnspecifiedBonds_normalize (mol : RawMolecule) (atom : Nat) :
    oxygenAt? (normalize mol).normalizeUnspecifiedBonds atom = oxygenAt? mol atom := by
  rw [oxygenAt?_normalizeUnspecifiedBonds, oxygenAt?_normalize]

theorem effectiveOxoBond?_normalizeUnspecifiedBonds_normalize
    (mol : RawMolecule) (bond : RawBond) :
    effectiveOxoBond? (normalize mol).normalizeUnspecifiedBonds bond =
      effectiveOxoBond? mol bond := by
  simp only [effectiveOxoBond?, effectiveOxoCenter?_normalizeUnspecifiedBonds_normalize,
    oxygenAt?_normalizeUnspecifiedBonds_normalize]

theorem chargeInsensitiveAtom?_normalizeUnspecifiedBonds_normalize
    (mol : RawMolecule) (index : Nat) :
    chargeInsensitiveAtom? (normalize mol).normalizeUnspecifiedBonds index =
      chargeInsensitiveAtom? mol index := by
  unfold chargeInsensitiveAtom?
  change
    ((mol.bonds.map (normalizeBond mol)).map
        (fun bond => (normalize mol).normalizeUnspecifiedBond bond)).any (fun bond =>
      effectiveOxoBond? ((normalize mol).normalizeUnspecifiedBonds) bond &&
        (bond.source == index || bond.target == index)) = _
  rw [List.any_map, List.any_map]
  congr 1
  funext bond
  change
    (effectiveOxoBond? ((normalize mol).normalizeUnspecifiedBonds)
          ((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond)) &&
        (((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond)).source == index ||
          ((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond)).target == index)) =
      (effectiveOxoBond? mol bond && (bond.source == index || bond.target == index))
  rw [effectiveOxoBond?_normalizeUnspecifiedBond_any,
    effectiveOxoBond?_normalizeBond_any,
    effectiveOxoBond?_normalizeUnspecifiedBonds_normalize,
    RawMolecule.normalizeUnspecifiedBond_source,
    RawMolecule.normalizeUnspecifiedBond_target,
    normalizeBond_source, normalizeBond_target]

theorem normalizeAtom_normalizeUnspecifiedBonds_normalize
    (mol : RawMolecule) (index : Nat) (atom : AtomSpec) :
    normalizeAtom (normalize mol).normalizeUnspecifiedBonds index
        (normalizeAtom (normalize mol) index
          (normalizeAtom mol index atom)) =
      normalizeAtom (normalize mol) index (normalizeAtom mol index atom) := by
  unfold normalizeAtom
  rw [chargeInsensitiveAtom?_normalizeUnspecifiedBonds_normalize,
    chargeInsensitiveAtom?_normalize]
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [insensitive, eligible]

theorem normalizeAtomsAux_normalizeUnspecifiedBonds_normalize
    (mol : RawMolecule) (offset : Nat) (atoms : List AtomSpec) :
    normalizeAtomsAux (normalize mol).normalizeUnspecifiedBonds offset
        (normalizeAtomsAux (normalize mol) offset (normalizeAtomsAux mol offset atoms)) =
      normalizeAtomsAux (normalize mol) offset (normalizeAtomsAux mol offset atoms) := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp only [normalizeAtomsAux]
      rw [normalizeAtom_normalizeUnspecifiedBonds_normalize, ih (offset + 1)]

/-- Pointwise form of the bridge for a single bond: once `N` has processed a bond and `U` has
resolved its kind, `N` leaves it unchanged. -/
theorem normalizeBond_normalizeUnspecifiedBond_normalize
    (mol : RawMolecule) (bond : RawBond) :
    normalizeBond (normalize mol).normalizeUnspecifiedBonds
        ((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond)) =
      (normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond) := by
  by_cases effective : effectiveOxoBond? mol bond = true
  · have bondEq : normalizeBond mol bond = { bond with kind := ParsedBondKind.single } :=
      normalizeBond_eq_single_of_effective mol bond effective
    have unresolved :
        (normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond) =
          normalizeBond mol bond := by
      rw [bondEq]
      exact RawMolecule.normalizeUnspecifiedBond_eq_self_of_resolved (normalize mol)
        { bond with kind := ParsedBondKind.single } (by simp)
    have effective' :
        effectiveOxoBond? (normalize mol).normalizeUnspecifiedBonds
            ((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond)) = true := by
      rw [unresolved, effectiveOxoBond?_normalizeBond_any,
        effectiveOxoBond?_normalizeUnspecifiedBonds_normalize, effective]
    have kindSingle :
        ((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond)).kind =
          ParsedBondKind.single := by
      rw [unresolved, bondEq]
    exact normalizeBond_eq_self_of_effective_of_kind_eq_single
      (normalize mol).normalizeUnspecifiedBonds
      ((normalize mol).normalizeUnspecifiedBond (normalizeBond mol bond))
      effective' kindSingle
  · have notEffective : effectiveOxoBond? mol bond = false := by
      cases observed : effectiveOxoBond? mol bond <;> simp_all
    have bondEq : normalizeBond mol bond = bond :=
      normalizeBond_eq_self_of_not_effective mol bond notEffective
    have effective' :
        effectiveOxoBond? (normalize mol).normalizeUnspecifiedBonds
            ((normalize mol).normalizeUnspecifiedBond bond) = false := by
      rw [effectiveOxoBond?_normalizeUnspecifiedBond_any,
        effectiveOxoBond?_normalizeUnspecifiedBonds_normalize, notEffective]
    rw [bondEq]
    exact normalizeBond_eq_self_of_not_effective
      (normalize mol).normalizeUnspecifiedBonds
      ((normalize mol).normalizeUnspecifiedBond bond) effective'

theorem map_normalizeBond_normalizeUnspecifiedBond (mol : RawMolecule)
    (bonds : List RawBond) :
    ((bonds.map (normalizeBond mol)).map
        ((normalize mol).normalizeUnspecifiedBond)).map
          (normalizeBond (normalize mol).normalizeUnspecifiedBonds) =
      (bonds.map (normalizeBond mol)).map
        ((normalize mol).normalizeUnspecifiedBond) := by
  induction bonds with
  | nil => rfl
  | cons bond rest ih =>
      simp only [List.map_cons]
      rw [normalizeBond_normalizeUnspecifiedBond_normalize, ih]





theorem normalize_normalizeUnspecifiedBonds_normalize (mol : RawMolecule) :
    normalize (normalize mol).normalizeUnspecifiedBonds =
      (normalize mol).normalizeUnspecifiedBonds := by
  apply rawMolecule_ext
  · have absorb : normalizeAtomsAux (normalize mol) 0
          (normalizeAtomsAux mol 0 mol.atoms) =
        normalizeAtomsAux mol 0 mol.atoms :=
      normalizeAtomsAux_normalize mol 0 mol.atoms
    have bridge := normalizeAtomsAux_normalizeUnspecifiedBonds_normalize mol 0 mol.atoms
    rw [absorb] at bridge
    change normalizeAtomsAux (normalize mol).normalizeUnspecifiedBonds 0
        (normalizeAtomsAux mol 0 mol.atoms) =
      normalizeAtomsAux mol 0 mol.atoms
    exact bridge
  · show ((mol.bonds.map (normalizeBond mol)).map
        ((normalize mol).normalizeUnspecifiedBond)).map
          (normalizeBond (normalize mol).normalizeUnspecifiedBonds) =
      (mol.bonds.map (normalizeBond mol)).map
        ((normalize mol).normalizeUnspecifiedBond)
    exact map_normalizeBond_normalizeUnspecifiedBond mol mol.bonds
  · rfl
  · rfl

/-! ## The production pipeline -/

/-- The `parsed` molecule of the production pipeline, isolated for reuse in the stability
statements. This is definitionally the production record's `parsed` field. -/
def p93Parsed (mol : RawMolecule) (cycles : List AromaticCycle := []) : RawMolecule :=
  (normalizeRawMoleculeP93 mol cycles).parsed

@[simp] theorem p93Parsed_eq (mol : RawMolecule) (cycles : List AromaticCycle) :
    p93Parsed mol cycles =
      (normalize (freezeSourceHydrogenCounts mol)).normalizeUnspecifiedBonds := by
  unfold p93Parsed
  exact normalizeRawMoleculeP93_parsed mol cycles

/-- The production parsed output lies in the explicit-hydrogen domain. -/
theorem p93Parsed_allExplicit (mol : RawMolecule) (cycles : List AromaticCycle) :
    AllExplicit (p93Parsed mol cycles) := by
  rw [p93Parsed_eq]
  exact allExplicit_normalizeUnspecifiedBonds _
    (allExplicit_normalize _ (allExplicit_freezeSourceHydrogenCounts mol))

/-- On its own output the freezing pass is the identity. -/
theorem p93Parsed_freeze_eq (mol : RawMolecule) (cycles : List AromaticCycle) :
    freezeSourceHydrogenCounts (p93Parsed mol cycles) = p93Parsed mol cycles :=
  freezeSourceHydrogenCounts_eq_self_of_allExplicit _
    (p93Parsed_allExplicit mol cycles)

/-- **Stability of the production parsed record.** One application followed by a second
application to the first output's `parsed` molecule returns the same parsed molecule. The cycle
list is arbitrary and is only carried along by the wrapper; it is never consulted for the parsed
record. -/
theorem p93Parsed_parsed_freeze (mol : RawMolecule) (cycles : List AromaticCycle) :
    p93Parsed (p93Parsed mol cycles) cycles = p93Parsed mol cycles := by
  have freezeEq : freezeSourceHydrogenCounts (p93Parsed mol cycles) = p93Parsed mol cycles :=
    p93Parsed_freeze_eq mol cycles
  rw [p93Parsed_eq (p93Parsed mol cycles) cycles, freezeEq, p93Parsed_eq mol cycles]
  rw [normalize_normalizeUnspecifiedBonds_normalize (freezeSourceHydrogenCounts mol)]
  exact normalizeUnspecifiedBonds_idempotent (normalize (freezeSourceHydrogenCounts mol))

/-- Functional form of the stability statement at a fixed cycle list. -/
theorem p93Parsed_comp_idempotent (cycles : List AromaticCycle) :
    (fun mol : RawMolecule => p93Parsed (p93Parsed mol cycles) cycles) =
      fun mol : RawMolecule => p93Parsed mol cycles := by
  funext mol
  exact p93Parsed_parsed_freeze mol cycles

/-- The raw `normalizeRawMolecule` wrapper is determined entirely by the parsed molecule, for any
cycle list: the other fields are all derived from the straightened molecule. -/
theorem normalizeRawMolecule_eq_of_parsed_eq (left right : RawMolecule)
    (cycles : List AromaticCycle)
    (parsedEq : left.normalizeUnspecifiedBonds = right.normalizeUnspecifiedBonds) :
    normalizeRawMolecule left cycles = normalizeRawMolecule right cycles := by
  unfold normalizeRawMolecule
  rw [parsedEq]

/-- **The production record is stable under a second pass.** Running the actual
`normalizeRawMoleculeP93` on the first output's parsed molecule, with the same arbitrary cycle
list, returns exactly the first `ChemistryNormalizationResult`. -/
theorem normalizeRawMoleculeP93_idempotent (mol : RawMolecule)
    (cycles : List AromaticCycle) :
    normalizeRawMoleculeP93 (normalizeRawMoleculeP93 mol cycles).parsed cycles =
      normalizeRawMoleculeP93 mol cycles := by
  unfold normalizeRawMoleculeP93
  apply normalizeRawMolecule_eq_of_parsed_eq
  change p93Parsed (p93Parsed mol cycles) cycles = p93Parsed mol cycles
  exact p93Parsed_parsed_freeze mol cycles

/-! ## Concrete parser provenance fixtures

The fixtures come from `P93SourceHydrogenFidelity`, where they are connected to the output of
`parseOpenSMILES` for `"P(=O)(O)(O)O"`, `"S(=O)(O)(O)O"`, etc. (the imported parse proofs for the
sulfur fixtures use `decide`). The statements below are therefore about actually parsed molecules,
not hand-invented ones. -/

/-- A second production pass over parsed phosphoric acid leaves the parsed molecule unchanged,
with the default (empty) cycle list. -/
theorem phosphoricAcid_parsed_stable :
    p93Parsed (p93Parsed P93SourceHydrogenFidelity.phosphoricAcidSource []) [] =
      p93Parsed P93SourceHydrogenFidelity.phosphoricAcidSource :=
  p93Parsed_parsed_freeze _ _

/-- The same stability with a nonempty aromatic cycle list, exercising the arbitrary-cycle
wrapper. -/
theorem phosphoricAcid_parsed_stable_nonempty_cycles :
    p93Parsed
        (p93Parsed P93SourceHydrogenFidelity.phosphoricAcidSource
          [{ atoms := [0, 1, 2] }])
        [{ atoms := [0, 1, 2] }] =
      p93Parsed P93SourceHydrogenFidelity.phosphoricAcidSource [{ atoms := [0, 1, 2] }] :=
  p93Parsed_parsed_freeze _ _

/-- A second production pass over parsed sulfuric acid is stable. -/
theorem sulfuricAcid_parsed_stable :
    p93Parsed (p93Parsed P93SourceHydrogenFidelity.sulfuricAcidSource []) [] =
      p93Parsed P93SourceHydrogenFidelity.sulfuricAcidSource :=
  p93Parsed_parsed_freeze _ _

/-- A second production pass over bracketed sulfur is stable. -/
theorem bracketedSulfur_parsed_stable :
    p93Parsed (p93Parsed P93SourceHydrogenFidelity.bracketedSulfurSource []) [] =
      p93Parsed P93SourceHydrogenFidelity.bracketedSulfurSource :=
  p93Parsed_parsed_freeze _ _

/-- A second production pass over hydrogen-bracketed sulfur is stable. -/
theorem hydrogenBracketedSulfur_parsed_stable :
    p93Parsed (p93Parsed P93SourceHydrogenFidelity.hydrogenBracketedSulfurSource []) [] =
      p93Parsed P93SourceHydrogenFidelity.hydrogenBracketedSulfurSource :=
  p93Parsed_parsed_freeze _ _

/-! ## Kernel-only audits -/

assert_kernel_only rawMolecule_ext
assert_kernel_only allExplicit_iff_allExplicitHydrogens
assert_kernel_only allExplicit_freezeSourceHydrogenCounts
assert_kernel_only allExplicit_normalize
assert_kernel_only allExplicit_normalizeUnspecifiedBonds
assert_kernel_only freezeSourceHydrogenCounts_eq_self_of_allExplicit
assert_kernel_only normalizeUnspecifiedBonds_idempotent
assert_kernel_only effectiveOxoCenter?_normalize
assert_kernel_only oxygenAt?_normalize
assert_kernel_only effectiveOxoBond?_normalizeBond
assert_kernel_only normalizeBond_eq_single_of_effective
assert_kernel_only normalizeBond_eq_self_of_not_effective
assert_kernel_only normalizeBond_eq_self_of_effective_of_kind_eq_single
assert_kernel_only chargeInsensitiveAtom?_normalize
assert_kernel_only normalizeAtom_normalize_apply
assert_kernel_only normalizeAtomsAux_normalize_apply
assert_kernel_only normalizeAtom_normalize
assert_kernel_only normalizeAtomsAux_normalize
assert_kernel_only normalizeAtoms_normalize
assert_kernel_only map_normalizeBond_normalizeBond
assert_kernel_only normalizeBond_normalize
assert_kernel_only normalize_bonds_normalize
assert_kernel_only normalize_normalize
assert_kernel_only effectiveOxoCenter?_normalizeUnspecifiedBonds
assert_kernel_only oxygenAt?_normalizeUnspecifiedBonds
assert_kernel_only effectiveOxoBond?_normalizeUnspecifiedBond_any
assert_kernel_only effectiveOxoBond?_normalizeBond_any
assert_kernel_only effectiveOxoCenter?_normalizeUnspecifiedBonds_normalize
assert_kernel_only oxygenAt?_normalizeUnspecifiedBonds_normalize
assert_kernel_only effectiveOxoBond?_normalizeUnspecifiedBonds_normalize
assert_kernel_only chargeInsensitiveAtom?_normalizeUnspecifiedBonds_normalize
assert_kernel_only normalizeAtom_normalizeUnspecifiedBonds_normalize
assert_kernel_only normalizeAtomsAux_normalizeUnspecifiedBonds_normalize
assert_kernel_only normalizeBond_normalizeUnspecifiedBond_normalize
assert_kernel_only map_normalizeBond_normalizeUnspecifiedBond
assert_kernel_only normalize_normalizeUnspecifiedBonds_normalize
assert_kernel_only p93Parsed_eq
assert_kernel_only p93Parsed_allExplicit
assert_kernel_only p93Parsed_freeze_eq
assert_kernel_only p93Parsed_parsed_freeze
assert_kernel_only p93Parsed_comp_idempotent
assert_kernel_only normalizeRawMolecule_eq_of_parsed_eq
assert_kernel_only normalizeRawMoleculeP93_idempotent
assert_kernel_only phosphoricAcid_parsed_stable
assert_kernel_only phosphoricAcid_parsed_stable_nonempty_cycles
assert_kernel_only sulfuricAcid_parsed_stable
assert_kernel_only bracketedSulfur_parsed_stable
assert_kernel_only hydrogenBracketedSulfur_parsed_stable

end P93NormalizationIdempotence
end OneCenter
end TetraStereo
