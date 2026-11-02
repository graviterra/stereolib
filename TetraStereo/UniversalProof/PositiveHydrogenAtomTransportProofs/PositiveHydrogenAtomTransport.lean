import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-!
# Original-atom index embedding and metadata transport under positive hydrogen demand

The production materializer `RawMolecule.withExplicitHydrogens` replaces every inline hydrogen count
by `some 0` and appends a real hydrogen atom for each implied hydrogen. The earlier record-identity
unit identified the *returned raw record* only under zero hydrogen demand, so it says nothing about
the case the materializer actually exists for: a molecule that demands hydrogens.

This module proves the transport that holds for **every** well-formed input molecule, with no demand
hypothesis at all, and then specialises to strictly positive demand:

* `withExplicitHydrogens_originalAtom` — every original index is retained at the same index in the
  actual expansion, carrying `materializedAtomSpec spec`. This is the original-atom index embedding.
* `withExplicitHydrogens_originalAtom_metadata` — the retained atom agrees with the source spec in
  element, isotope, charge, aromaticity, tetrahedral input parity and allowed-valence table, and its
  inline count is exactly the consumed `some 0`.
* `withExplicitHydrogens_freshAtom` — every atom at an index at or above `mol.atomCount` in the
  actual expansion is an ordinary aliphatic hydrogen whose incident bond order is one.
* `atomCount_lt_of_positiveHydrogenDemand` / `withExplicitHydrogens_boundary_hydrogen` — under
  strictly positive demand the actual atom count *strictly* grows and the first appended hydrogen is
  exactly the atom at index `mol.atomCount`.

Two fully closed witnesses inhabit the positive-demand domain: a hand-built `[C@@H](F)(Cl)Br`
centre (one inline hydrogen plus a written parity, three halide neighbours) and a single unbracketed
organic carbon, whose four hydrogens come from the default-valence policy rather than an inline
count. Both are used only for transformation nonvacuity; neither carries a stereochemical or
scientific claim.

The only source input condition is `WellFormed`, which the expansion genuinely consumes: it is what
rules out a stale bond record mentioning a fresh hydrogen index before that hydrogen exists. No
descriptor, output descriptor, successful compiler, expected result, expansion equation or zero-
demand hypothesis is supplied by a caller.

TECHNICAL_PROOF_REQUIRED: exact bond-source provenance from a demanding atom to its materialized
hydrogens (which fresh index belongs to which demanding source atom), the running-length bookkeeping
that identifies the appended block with its demanding index, public runtime/parser output refinement
and source-wide mixed planar integration. HUMAN_REVIEW_REQUIRED: chemical reading of inline counts,
default-valence fill and written parity conventions. EXTERNAL_EVIDENCE_REQUIRED: adoption of the
default-valence table against an authoritative specification. No scientific approval is asserted.
-/

/-! ## Positive hydrogen demand -/

/-- The actual materializer requests at least one new hydrogen at an actual input index.

This is the complement of the zero-demand hypothesis used by the earlier record-identity unit. No
theorem in this module assumes it away; it is the *additional* hypothesis that makes the fresh-atom
consequences strict. -/
def PositiveHydrogenDemand (molecule : RawMolecule) : Prop :=
  ∃ index, index < molecule.atomCount ∧ 0 < molecule.hydrogenCountAt index

/-- A pointwise-positive entry makes a mapped list sum positive. -/
theorem list_sum_map_pos {α : Type*} (f : α → ℕ) (values : List α) (index : α)
    (member : index ∈ values) (positive : 0 < f index) :
    0 < (values.map f).sum := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp member with rfl | inTail
      · omega
      · have tailPositive := inductionHypothesis inTail
        omega

/-! ## Atom-list growth of one accumulation step -/

/-- One accumulation step appends exactly the demanding atom's implied hydrogen count to the atom
list, and appends nothing when that count is zero. -/
theorem withExplicitHydrogensStep_atoms_length
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ) :
    (withExplicitHydrogensStep mol state idx).1.length =
      state.1.length + mol.hydrogenCountAt idx := by
  by_cases zero : mol.hydrogenCountAt idx == 0
  · have countZero : mol.hydrogenCountAt idx = 0 := by simpa using zero
    simp [withExplicitHydrogensStep, countZero]
  · simp only [withExplicitHydrogensStep, if_neg zero]
    simp [List.length_append, List.length_replicate]

/-- The accumulation fold grows the atom list by the total implied hydrogen count of the processed
indices, independently of any zero-demand assumption. -/
theorem fold_withExplicitHydrogensStep_atoms_length
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState) :
    (indices.foldl (withExplicitHydrogensStep mol) state).1.length =
      state.1.length + (indices.map mol.hydrogenCountAt).sum := by
  induction indices generalizing state with
  | nil => simp
  | cons index rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis (withExplicitHydrogensStep mol state index)]
      simp only [List.map_cons, List.sum_cons]
      rw [withExplicitHydrogensStep_atoms_length]
      omega

/-! ## Bridges from the returned record to the accumulator

`withExplicitHydrogens` finishes by canonicalizing only the written-neighbour table. The atom list,
the bond list and therefore the atom-count and incident-bond-order observations are the accumulator's.
These three lemmas state that literally, so later proofs rewrite instead of unfolding the whole
pipeline. -/

theorem withExplicitHydrogens_atomAt?_eq (mol : RawMolecule) (index : ℕ) :
    mol.withExplicitHydrogens.atomAt? index =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? index := by
  simp [withExplicitHydrogens, withExactWrittenNeighbors, atomAt?]

theorem withExplicitHydrogens_incidentBondOrderSum_eq (mol : RawMolecule) (index : ℕ) :
    mol.withExplicitHydrogens.incidentBondOrderSum index =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.incidentBondOrderSum index := by
  simp [withExplicitHydrogens, withExactWrittenNeighbors, incidentBondOrderSum]

theorem withExplicitHydrogens_atomCount_eq_fold (mol : RawMolecule) :
    mol.withExplicitHydrogens.atomCount =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomCount := by
  simp [withExplicitHydrogens, withExactWrittenNeighbors, atomCount]

/-- The accumulator's atom count is the source count plus the total implied hydrogen demand. -/
theorem hydrogenExpansionFold_atomCount_eq (mol : RawMolecule) :
    ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomCount =
      mol.atomCount + ((List.range mol.atomCount).map mol.hydrogenCountAt).sum := by
  have lengthLemma := fold_withExplicitHydrogensStep_atoms_length mol (List.range mol.atomCount)
    (initialHydrogenExpansionState mol)
  simpa [atomCount, HydrogenExpansionState.toRawMolecule, initialHydrogenExpansionState,
    List.length_map] using lengthLemma

/-- The actual expanded molecule has exactly the source atom count plus the total implied hydrogen
demand. -/
theorem withExplicitHydrogens_atomCount_eq (mol : RawMolecule) :
    mol.withExplicitHydrogens.atomCount =
      mol.atomCount + ((List.range mol.atomCount).map mol.hydrogenCountAt).sum := by
  rw [withExplicitHydrogens_atomCount_eq_fold, hydrogenExpansionFold_atomCount_eq]

/-- Expansion never removes an original index, with or without demand. -/
theorem withExplicitHydrogens_atomCount_le (mol : RawMolecule) :
    mol.atomCount ≤ mol.withExplicitHydrogens.atomCount := by
  rw [withExplicitHydrogens_atomCount_eq]
  omega

/-- Strictly positive demand strictly grows the actual atom count. -/
theorem atomCount_lt_of_positiveHydrogenDemand (mol : RawMolecule)
    (demand : PositiveHydrogenDemand mol) :
    mol.atomCount < mol.withExplicitHydrogens.atomCount := by
  obtain ⟨index, bound, positive⟩ := demand
  have sumPositive : 0 < ((List.range mol.atomCount).map mol.hydrogenCountAt).sum :=
    list_sum_map_pos mol.hydrogenCountAt (List.range mol.atomCount) index
      (List.mem_range.mpr bound) positive
  rw [withExplicitHydrogens_atomCount_eq]
  omega

/-! ## Original-atom index embedding and metadata preservation -/

/-- The materialized-valence invariant is preserved by the complete production fold for every
well-formed source molecule. This is the positive-demand generalisation of the accumulator invariant:
the signature carries no demand hypothesis. -/
theorem hydrogenExpansionFold_materializedValenceInvariant (mol : RawMolecule)
    (well : mol.WellFormed) :
    ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).MaterializedValenceInvariant mol := by
  have initialWell : (initialHydrogenExpansionState mol).toRawMolecule.WellFormed := by
    intro bond member
    simpa [BondEndpointsOK] using well bond member
  exact fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro index member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol) initialWell
    (initialHydrogenExpansionState_materializedValenceInvariant mol)

/-- Original-atom index embedding: every source index is present in the actual expansion at the same
index, carrying the materialized version of the source specification. -/
theorem withExplicitHydrogens_originalAtom (mol : RawMolecule) (well : mol.WellFormed)
    (index : ℕ) (spec : AtomSpec) (lookup : mol.atomAt? index = some spec) :
    mol.withExplicitHydrogens.atomAt? index = some (materializedAtomSpec spec) := by
  have key := (hydrogenExpansionFold_materializedValenceInvariant mol well).originalAtom
    index spec lookup
  rw [withExplicitHydrogens_atomAt?_eq]
  exact key

/-- Every real source index resolves in the actual expansion. -/
theorem withExplicitHydrogens_originalIndex_isAtom (mol : RawMolecule) (well : mol.WellFormed)
    (index : ℕ) (bound : index < mol.atomCount) :
    ∃ out, mol.withExplicitHydrogens.atomAt? index = some out := by
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt mol.atoms index bound
  exact ⟨materializedAtomSpec spec,
    withExplicitHydrogens_originalAtom mol well index spec (by simpa [atomAt?] using lookup)⟩

/-- Complete metadata actually observed at an original index after expansion. Only the inline count
is consumed; every other source fact is transported verbatim. -/
structure OriginalAtomMetadata (mol : RawMolecule) (index : ℕ) (spec out : AtomSpec) : Prop where
  observed : mol.withExplicitHydrogens.atomAt? index = some out
  elementPreserved : out.element = spec.element
  isotopePreserved : out.isotope? = spec.isotope?
  chargePreserved : out.charge = spec.charge
  aromaticPreserved : out.aromatic = spec.aromatic
  tetrahedralPreserved : out.tetrahedral? = spec.tetrahedral?
  allowedValencesPreserved : out.allowedValences = spec.allowedValences
  inlineConsumed : out.explicitHydrogens? = some 0

/-- Atom metadata preservation from the actual expansion at every original index. -/
theorem withExplicitHydrogens_originalAtom_metadata (mol : RawMolecule) (well : mol.WellFormed)
    (index : ℕ) (spec : AtomSpec) (lookup : mol.atomAt? index = some spec) :
    OriginalAtomMetadata mol index spec (materializedAtomSpec spec) :=
  ⟨withExplicitHydrogens_originalAtom mol well index spec lookup,
    materializedAtomSpec_element spec,
    materializedAtomSpec_isotope spec,
    materializedAtomSpec_charge spec,
    materializedAtomSpec_aromatic spec,
    materializedAtomSpec_tetrahedral spec,
    materializedAtomSpec_allowedValences spec,
    rfl⟩

/-- The original-atom index embedding as a `Fin` map into the actual expansion. -/
def originalIndexEmbedding (mol : RawMolecule) (index : Fin mol.atomCount) :
    Fin mol.withExplicitHydrogens.atomCount :=
  ⟨index.val, lt_of_lt_of_le index.isLt (withExplicitHydrogens_atomCount_le mol)⟩

/-- The embedding sends a real source atom to its materialized specification. -/
theorem originalIndexEmbedding_atomAt? (mol : RawMolecule) (well : mol.WellFormed)
    (index : Fin mol.atomCount) (spec : AtomSpec) (lookup : mol.atomAt? index.val = some spec) :
    mol.withExplicitHydrogens.atomAt? (originalIndexEmbedding mol index).val =
      some (materializedAtomSpec spec) :=
  withExplicitHydrogens_originalAtom mol well index.val spec lookup

/-! ## Fresh hydrogen atoms under positive demand -/

/-- Every atom at or beyond the source count in the actual expansion is an ordinary aliphatic
hydrogen with incident bond order one. No demand hypothesis is needed for this clause. -/
theorem withExplicitHydrogens_freshAtom (mol : RawMolecule) (well : mol.WellFormed)
    (index : ℕ) (atom : AtomSpec) (lower : mol.atomCount ≤ index)
    (lookup : mol.withExplicitHydrogens.atomAt? index = some atom) :
    atom = AtomSpec.aliphatic Element.H ∧
      mol.withExplicitHydrogens.incidentBondOrderSum index = 1 := by
  have foldLookup :
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? index = some atom := by
    rwa [← withExplicitHydrogens_atomAt?_eq]
  have fresh := (hydrogenExpansionFold_materializedValenceInvariant mol well).freshAtom
    index atom lower foldLookup
  refine ⟨fresh.1, ?_⟩
  rw [withExplicitHydrogens_incidentBondOrderSum_eq]
  exact fresh.2

/-- Under strictly positive demand the first appended atom of the actual expansion is exactly the
ordinary hydrogen at index `mol.atomCount`. -/
theorem withExplicitHydrogens_boundary_hydrogen (mol : RawMolecule) (well : mol.WellFormed)
    (demand : PositiveHydrogenDemand mol) :
    mol.withExplicitHydrogens.atomAt? mol.atomCount = some (AtomSpec.aliphatic Element.H) := by
  have growth := atomCount_lt_of_positiveHydrogenDemand mol demand
  obtain ⟨atom, lookup⟩ := listGet?_exists_of_lt mol.withExplicitHydrogens.atoms mol.atomCount
    (by simpa [atomCount] using growth)
  have lookupAt : mol.withExplicitHydrogens.atomAt? mol.atomCount = some atom := by
    simpa [atomAt?] using lookup
  have fresh := withExplicitHydrogens_freshAtom mol well mol.atomCount atom
    (Nat.le_refl mol.atomCount) lookupAt
  rw [← fresh.1]
  exact lookupAt

/-- Existential form: a strictly positive-demand expansion contains a real fresh hydrogen atom whose
incident bond order is one. -/
theorem exists_freshHydrogen_of_positiveHydrogenDemand (mol : RawMolecule) (well : mol.WellFormed)
    (demand : PositiveHydrogenDemand mol) :
    ∃ index, mol.atomCount ≤ index ∧
      mol.withExplicitHydrogens.atomAt? index = some (AtomSpec.aliphatic Element.H) ∧
      mol.withExplicitHydrogens.incidentBondOrderSum index = 1 := by
  refine ⟨mol.atomCount, Nat.le_refl _,
    withExplicitHydrogens_boundary_hydrogen mol well demand, ?_⟩
  exact (withExplicitHydrogens_freshAtom mol well mol.atomCount (AtomSpec.aliphatic Element.H)
    (Nat.le_refl _) (withExplicitHydrogens_boundary_hydrogen mol well demand)).2

/-! ## Closed nonzero-demand witnesses

Both witnesses are closed records: the demand value is forced by the inline count or by the
default-valence table, and every conclusion below is an instance of the general theorems. Their
purpose is transformation nonvacuity, not a chemical or stereochemical assignment claim. -/

/-- The bracket carbon of `[C@@H](F)(Cl)Br`: one inline hydrogen and a written parity, bonded to
fluorine, chlorine and bromine. Its graph degree is three, which is exactly why degree-based centre
detection never fires on parser output before materialization. -/
def bracketCenterSpec : AtomSpec :=
  { AtomSpec.aliphatic Element.C with
      explicitHydrogens? := some 1, tetrahedral? := some .clockwise }

/-- A hand-built `[C@@H](F)(Cl)Br` shape with a total written-neighbour table. -/
def bracketCarbonHalide : RawMolecule :=
  { atoms :=
      [bracketCenterSpec,
       { AtomSpec.aliphatic Element.F with explicitHydrogens? := some 0 },
       { AtomSpec.aliphatic Element.Cl with explicitHydrogens? := some 0 },
       { AtomSpec.aliphatic Element.Br with explicitHydrogens? := some 0 }]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩]
    neighborOrder := [[1, 2, 3], [0], [0], [0]] }

theorem bracketCarbonHalide_atomCount : bracketCarbonHalide.atomCount = 4 := by
  simp [bracketCarbonHalide, atomCount]

theorem bracketCarbonHalide_wellFormed : bracketCarbonHalide.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide

theorem bracketCarbonHalide_centerSpec_lookup :
    bracketCarbonHalide.atomAt? 0 = some bracketCenterSpec := rfl

/-- The bracket centre demands exactly its one inline hydrogen. -/
theorem bracketCarbonHalide_centerHydrogens : bracketCarbonHalide.hydrogenCountAt 0 = 1 := by
  decide

theorem bracketCarbonHalide_positiveHydrogenDemand :
    PositiveHydrogenDemand bracketCarbonHalide := by
  refine ⟨0, ?_, ?_⟩
  · rw [bracketCarbonHalide_atomCount]; omega
  · rw [bracketCarbonHalide_centerHydrogens]; omega

/-- The actual bracket-centre expansion grows beyond its four original C/F/Cl/Br atoms because
the centre demands a materialized hydrogen. -/
theorem bracketCarbonHalide_expansion_grows :
    bracketCarbonHalide.atomCount < bracketCarbonHalide.withExplicitHydrogens.atomCount :=
  atomCount_lt_of_positiveHydrogenDemand _ bracketCarbonHalide_positiveHydrogenDemand

/-- The first appended atom of the actual bracket-centre expansion is hydrogen. -/
theorem bracketCarbonHalide_expansion_boundary_hydrogen :
    bracketCarbonHalide.withExplicitHydrogens.atomAt? bracketCarbonHalide.atomCount =
      some (AtomSpec.aliphatic Element.H) :=
  withExplicitHydrogens_boundary_hydrogen _ bracketCarbonHalide_wellFormed
    bracketCarbonHalide_positiveHydrogenDemand

/-- The bracket centre survives materialization at index zero with its full source metadata. -/
theorem bracketCarbonHalide_center_metadata :
    OriginalAtomMetadata bracketCarbonHalide 0 bracketCenterSpec
      (materializedAtomSpec bracketCenterSpec) :=
  withExplicitHydrogens_originalAtom_metadata _ bracketCarbonHalide_wellFormed 0
    bracketCenterSpec bracketCarbonHalide_centerSpec_lookup

/-- The materialized centre keeps the carbon element. -/
theorem bracketCarbonHalide_expanded_center_element :
    (materializedAtomSpec bracketCenterSpec).element = Element.C := rfl

/-- The materialized centre keeps the written tetrahedral parity; materialization does not consume
the annotation, only the inline count. -/
theorem bracketCarbonHalide_expanded_center_tetrahedral :
    (materializedAtomSpec bracketCenterSpec).tetrahedral? =
      some TetrahedralInputParity.clockwise := rfl

/-- The materialized centre's inline count has been consumed to `some 0`, so `usedValenceAt` cannot
count the hydrogen twice. -/
theorem bracketCarbonHalide_expanded_center_inlineConsumed :
    (materializedAtomSpec bracketCenterSpec).explicitHydrogens? = some 0 := rfl

/-- A single unbracketed organic carbon with no bonds. Its four hydrogens are demanded by the
default-valence policy, not by an inline count, so it exercises the other half of the demand
surface. -/
def unbracketedCarbon : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C], bonds := [], neighborOrder := [[]] }

theorem unbracketedCarbon_atomCount : unbracketedCarbon.atomCount = 1 := by
  simp [unbracketedCarbon, atomCount]

theorem unbracketedCarbon_wellFormed : unbracketedCarbon.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide

/-- The default-valence policy fills the unbracketed carbon to four hydrogens. -/
theorem unbracketedCarbon_hydrogenCountAt : unbracketedCarbon.hydrogenCountAt 0 = 4 := by
  decide

theorem unbracketedCarbon_positiveHydrogenDemand :
    PositiveHydrogenDemand unbracketedCarbon := by
  refine ⟨0, ?_, ?_⟩
  · rw [unbracketedCarbon_atomCount]; omega
  · rw [unbracketedCarbon_hydrogenCountAt]; omega

/-- The unbracketed carbon's expansion grows by its four implied hydrogens. -/
theorem unbracketedCarbon_expansion_grows :
    unbracketedCarbon.atomCount < unbracketedCarbon.withExplicitHydrogens.atomCount :=
  atomCount_lt_of_positiveHydrogenDemand _ unbracketedCarbon_positiveHydrogenDemand

/-- The source carbon is retained at index zero, with its implicit-count field consumed. -/
theorem unbracketedCarbon_original_atom :
    unbracketedCarbon.withExplicitHydrogens.atomAt? 0 =
      some (materializedAtomSpec (AtomSpec.aliphatic Element.C)) :=
  withExplicitHydrogens_originalAtom _ unbracketedCarbon_wellFormed 0
    (AtomSpec.aliphatic Element.C) rfl

end TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport
