import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-!
  Materialising implicit hydrogens as parsed atoms.

  A stereocentre written `[C@@H]` has graph degree three, because its hydrogen is a bracket count
  rather than an atom.  Degree-based centre detection therefore never fires on parser output, which
  is the single reason the parser and the stereochemistry layers were never connected.

  Materialisation is not just "append hydrogens".  OpenSMILES parity is stated against the order the
  neighbours were *written*, and a bracket hydrogen occupies the position immediately after the atom
  the centre was reached from — or first, when the centre opens the string.  Hydrogen bonds are
  therefore spliced into the bond list at that position, so that reading neighbours back out of
  bond order reproduces the order the parity refers to.  Appending them instead would silently
  permute the neighbour order and mirror every affected descriptor.
-/

namespace RawMolecule

/-- Atom metadata after its inline hydrogen count has been represented by actual atoms and bonds.

The input parity, isotope, charge, element, and aromatic flag remain source facts. Only the inline
count is consumed: retaining it would make `usedValenceAt` count every materialized hydrogen twice.
-/
def materializedAtomSpec (atom : AtomSpec) : AtomSpec :=
  { atom with explicitHydrogens? := some 0 }

@[simp] theorem materializedAtomSpec_element (atom : AtomSpec) :
    (materializedAtomSpec atom).element = atom.element := rfl

@[simp] theorem materializedAtomSpec_isotope (atom : AtomSpec) :
    (materializedAtomSpec atom).isotope? = atom.isotope? := rfl

@[simp] theorem materializedAtomSpec_charge (atom : AtomSpec) :
    (materializedAtomSpec atom).charge = atom.charge := rfl

@[simp] theorem materializedAtomSpec_aromatic (atom : AtomSpec) :
    (materializedAtomSpec atom).aromatic = atom.aromatic := rfl

@[simp] theorem materializedAtomSpec_tetrahedral (atom : AtomSpec) :
    (materializedAtomSpec atom).tetrahedral? = atom.tetrahedral? := rfl

@[simp] theorem materializedAtomSpec_explicitHydrogens (atom : AtomSpec) :
    (materializedAtomSpec atom).explicitHydrogens = 0 := rfl

@[simp] theorem materializedAtomSpec_allowedValences (atom : AtomSpec) :
    (materializedAtomSpec atom).allowedValences = atom.allowedValences := by
  simp [materializedAtomSpec, AtomSpec.allowedValences]

/-- OpenSMILES organic-subset default valences, used to imply hydrogen counts.

`AtomSpec.allowedValences` is a *permissive* table for validation: it lists every acceptable
valence, so oxygen admits `1`, `2` and `3`.  `implicitHydrogensAt?` selects the first entry at or
above the valence already used, which on a permissive table fills to the *minimum* acceptable
valence — and so gives a hydroxyl oxygen no hydrogen at all, silently turning `C(=O)O` into a
carboxylate skeleton.  Implying hydrogens needs the standard valence the organic subset fills to,
which is what this table records.  The permissive table remains correct for validation. -/
def elementDefaultValences : Element → List ℕ
  | Element.wildcard => []
  | Element.H => [1]
  | Element.B => [3]
  | Element.C => [4]
  | Element.N => [3]
  | Element.O => [2]
  | Element.F => [1]
  | Element.P => [3, 5]
  | Element.S => [2, 4, 6]
  | Element.Na => [1]
  | Element.Si => [4]
  | Element.Ge => [4]
  | Element.As => [3, 5]
  | Element.Se => [2, 4, 6]
  | Element.Sn => [2, 4]
  | Element.Sb => [3, 5]
  | Element.Te => [2, 4, 6]
  | Element.Pb => [2, 4]
  | Element.Bi => [3, 5]
  | Element.Cl => [1]
  | Element.Br => [1]
  | Element.I => [1]

/-- Default fill valence for a parsed atom, respecting aromaticity.

An aromatic ring atom fills to the aromatic valence, not the aliphatic one.  Aromatic bonds are
normalised to order 1 here, so an unsubstituted aromatic carbon shows two bonds; filling it to
carbon's aliphatic valence of four would give it two hydrogens instead of one and inflate benzene to
`C₆H₁₂`. -/
def defaultValences (spec : AtomSpec) : List ℕ :=
  if spec.aromatic then
    match spec.element with
    | Element.C | Element.B => [3]
    -- A two-connected aromatic ring heteroatom is the pyridine/furan/thiophene type and carries no
    -- hydrogen; the pyrrole type is written `[nH]` and supplies its own.
    | Element.N | Element.O | Element.S | Element.P => [2]
    | Element.wildcard => []
    | other => elementDefaultValences other
  else
    elementDefaultValences spec.element

/-- Total hydrogens attached to an atom under the OpenSMILES implicit-hydrogen policy.

A bracket atom carries an exact count (`some n`), including `some 0` when no `H` suffix was written.
Only an unbracketed organic-subset atom (`none`) is filled to its standard valence. -/
def hydrogenCountAt (mol : RawMolecule) (idx : ℕ) : ℕ :=
  match mol.atomAt? idx with
  | none => 0
  | some spec =>
      match spec.explicitHydrogens? with
      | some count => count
      | none =>
          let used := mol.incidentBondOrderSum idx
          match (defaultValences spec).find? fun valence => used ≤ valence with
          | some valence => valence - used
          | none => 0

/-- Insert `extra` immediately after the first bond satisfying `p`. -/
def insertAfterFirst (p : RawBond → Bool) (extra : List RawBond) :
    List RawBond → Option (List RawBond)
  | [] => none
  | bond :: rest =>
      if p bond then some (bond :: (extra ++ rest))
      else (insertAfterFirst p extra rest).map (fun out => bond :: out)

theorem insertAfterFirst_eq_some_perm
    (p : RawBond → Bool) (extra bonds out : List RawBond)
    (observed : insertAfterFirst p extra bonds = some out) :
    out.Perm (bonds ++ extra) := by
  induction bonds generalizing out with
  | nil => simp [insertAfterFirst] at observed
  | cons bond rest ih =>
      simp only [insertAfterFirst] at observed
      split at observed
      · cases observed
        exact List.Perm.cons bond
          (List.perm_append_comm (l₁ := extra) (l₂ := rest))
      · cases mapped : insertAfterFirst p extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            exact List.Perm.cons bond (ih tail mapped)

/-- Insert `extra` immediately before the first bond satisfying `p`. -/
def insertBeforeFirst (p : RawBond → Bool) (extra : List RawBond) :
    List RawBond → Option (List RawBond)
  | [] => none
  | bond :: rest =>
      if p bond then some (extra ++ bond :: rest)
      else (insertBeforeFirst p extra rest).map (fun out => bond :: out)

theorem insertBeforeFirst_eq_some_perm
    (p : RawBond → Bool) (extra bonds out : List RawBond)
    (observed : insertBeforeFirst p extra bonds = some out) :
    out.Perm (bonds ++ extra) := by
  induction bonds generalizing out with
  | nil => simp [insertBeforeFirst] at observed
  | cons bond rest ih =>
      simp only [insertBeforeFirst] at observed
      split at observed
      · cases observed
        exact List.perm_append_comm (l₁ := extra) (l₂ := bond :: rest)
      · cases mapped : insertBeforeFirst p extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            exact List.Perm.cons bond (ih tail mapped)

/-- Splice one atom's hydrogen bonds into the bond list at the position OpenSMILES gives them.

A bracket hydrogen is the neighbour immediately following the atom the centre was reached from, so
its bond goes directly after the bond that arrives at the centre.  When the centre opens the string
and has no preceding atom, the hydrogen is the first neighbour instead, so its bond goes before the
centre's first outgoing bond. -/
def spliceHydrogenBonds (bonds : List RawBond) (idx : ℕ) (extra : List RawBond) : List RawBond :=
  if extra.isEmpty then
    bonds
  else
    match insertAfterFirst (fun bond => bond.target == idx) extra bonds with
    | some out => out
    | none =>
        match insertBeforeFirst (fun bond => bond.source == idx) extra bonds with
        | some out => out
        | none => bonds ++ extra

/-- Splicing changes only bond-list order; it preserves exactly the old bonds plus the new
hydrogen bonds. -/
theorem spliceHydrogenBonds_perm
    (bonds : List RawBond) (idx : ℕ) (extra : List RawBond) :
    (spliceHydrogenBonds bonds idx extra).Perm (bonds ++ extra) := by
  unfold spliceHydrogenBonds
  split
  · rename_i empty
    have extraNil : extra = [] := List.isEmpty_iff.mp empty
    subst extra
    simp
  · cases after : insertAfterFirst (fun bond => bond.target == idx) extra bonds with
    | some out => exact insertAfterFirst_eq_some_perm _ _ _ _ after
    | none =>
        cases before : insertBeforeFirst (fun bond => bond.source == idx) extra bonds with
        | some out => exact insertBeforeFirst_eq_some_perm _ _ _ _ before
        | none => exact List.Perm.refl _

/-- Source-aware bond splice. Missing metadata retains the legacy hand-built convention; a
known component root inserts before its first incident edge, including a ring arriving from another
component. A nonroot inserts after its exact introduction edge, never after an earlier ring closure.
The append fallback keeps this low-level total function defined for inconsistent hand-built records;
checked source intake rejects such metadata before authority claims. -/
def spliceHydrogenBondsWithPredecessor (predecessor : Option (Option ℕ))
    (bonds : List RawBond) (idx : ℕ) (extra : List RawBond) : List RawBond :=
  if extra.isEmpty then bonds
  else
    match predecessor with
    | none => spliceHydrogenBonds bonds idx extra
    | some none =>
        (insertBeforeFirst (fun bond => bond.source == idx || bond.target == idx)
          extra bonds).getD (bonds ++ extra)
    | some (some parent) =>
        (insertAfterFirst (fun bond => bond.source == parent && bond.target == idx)
          extra bonds).getD (bonds ++ extra)

theorem spliceHydrogenBondsWithPredecessor_perm
    (predecessor : Option (Option ℕ)) (bonds : List RawBond) (idx : ℕ)
    (extra : List RawBond) :
    (spliceHydrogenBondsWithPredecessor predecessor bonds idx extra).Perm (bonds ++ extra) := by
  unfold spliceHydrogenBondsWithPredecessor
  split
  · rename_i empty
    have extraNil : extra = [] := List.isEmpty_iff.mp empty
    subst extra
    simp
  · cases predecessor with
    | none => exact spliceHydrogenBonds_perm _ _ _
    | some parent =>
        cases parent with
        | none =>
            cases inserted : insertBeforeFirst
                (fun bond => bond.source == idx || bond.target == idx) extra bonds with
            | none => exact List.Perm.refl _
            | some out => exact insertBeforeFirst_eq_some_perm _ _ _ _ inserted
        | some parent =>
            change ((insertAfterFirst
              (fun bond => bond.source == parent && bond.target == idx) extra bonds).getD
                (bonds ++ extra)).Perm (bonds ++ extra)
            cases inserted : insertAfterFirst
                (fun bond => bond.source == parent && bond.target == idx) extra bonds with
            | none => exact List.Perm.refl _
            | some out => exact insertAfterFirst_eq_some_perm _ _ _ _ inserted

/-- Read source introduction history when present. Incoming ring edges alone do not establish
that a source atom had a predecessor. The bond-list heuristic remains only for legacy raw records. -/
def hydrogenHasPreceding (mol : RawMolecule) (idx : ℕ) : Bool :=
  match mol.introductionPredecessors[idx]? with
  | some parent => parent.isSome
  | none => mol.bonds.any fun bond => bond.target == idx

/-- Insert a materialised hydrogen into one atom's written neighbour order.

OpenSMILES puts a bracket hydrogen immediately after the atom the centre was reached from, or first
when the centre opens the string.  `hasPreceding` distinguishes those cases. -/
def insertHydrogenInOrder (order : List ℕ) (hasPreceding : Bool) (hydrogens : List ℕ) : List ℕ :=
  if hasPreceding then
    match order with
    | [] => hydrogens
    | first :: rest => first :: (hydrogens ++ rest)
  else
    hydrogens ++ order

/-- Hydrogen placement preserves exact membership; it only moves the fresh block to its
OpenSMILES parity position. -/
theorem insertHydrogenInOrder_perm (order : List ℕ) (hasPreceding : Bool)
    (hydrogens : List ℕ) :
    (insertHydrogenInOrder order hasPreceding hydrogens).Perm (hydrogens ++ order) := by
  cases hasPreceding <;> cases order <;> simp [insertHydrogenInOrder]
  rename_i head tail
  induction hydrogens with
  | nil => simp
  | cons hydrogen rest ih =>
      exact (List.Perm.swap hydrogen head (rest ++ tail)).trans
        (List.Perm.cons hydrogen ih)

theorem freshHydrogenIds_nodup (base count : ℕ) :
    ((List.range count).map fun offset => base + offset).Nodup := by
  exact List.nodup_range.map (by
    intro first second equal
    exact Nat.add_left_cancel equal)

theorem freshHydrogenId_bounds (base count hydrogen : ℕ)
    (member : hydrogen ∈ (List.range count).map fun offset => base + offset) :
    base ≤ hydrogen ∧ hydrogen < base + count := by
  rcases List.mem_map.mp member with ⟨offset, offsetMem, rfl⟩
  exact ⟨Nat.le_add_right base offset,
    Nat.add_lt_add_left (List.mem_range.mp offsetMem) base⟩

theorem listGet?_append_left_of_lt {α : Type*} (left right : List α) (index : ℕ)
    (bound : index < left.length) :
    listGet? (left ++ right) index = listGet? left index := by
  induction left generalizing index with
  | nil => simp at bound
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at bound
          simpa [listGet?] using inductionHypothesis index bound

theorem listGet?_append_right_of_length_le {α : Type*} (left right : List α) (index : ℕ)
    (bound : left.length ≤ index) :
    listGet? (left ++ right) index = listGet? right (index - left.length) := by
  induction left generalizing index with
  | nil => simp
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => simp at bound
      | succ index =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
          simpa [listGet?, Nat.succ_sub_succ_eq_sub] using
            inductionHypothesis index bound

theorem listGet?_map {α β : Type*} (transform : α → β) (values : List α) (index : ℕ) :
    listGet? (values.map transform) index = (listGet? values index).map transform := by
  induction values generalizing index with
  | nil => simp [listGet?]
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => simpa [listGet?] using inductionHypothesis index

/-- Accumulator used while implicit hydrogens are materialized. -/
abbrev HydrogenExpansionState := List AtomSpec × List RawBond × List (List ℕ)

/-- Regard an expansion accumulator as the raw molecule it currently represents. -/
def HydrogenExpansionState.toRawMolecule (state : HydrogenExpansionState) : RawMolecule :=
  { atoms := state.1, bonds := state.2.1, neighborOrder := state.2.2 }

/-- Initial accumulator with a total written-neighbour table, including the documented fallback
for hand-built molecules. -/
def initialHydrogenExpansionState (mol : RawMolecule) : HydrogenExpansionState :=
  (mol.atoms.map materializedAtomSpec, mol.bonds,
    (List.range mol.atomCount).map mol.writtenNeighbors)

@[simp] theorem initialHydrogenExpansionState_atomCount (mol : RawMolecule) :
    (initialHydrogenExpansionState mol).toRawMolecule.atomCount = mol.atomCount := by
  simp [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule, atomCount]

@[simp] theorem initialHydrogenExpansionState_bondOrder
    (mol : RawMolecule) (left right : ℕ) :
    (initialHydrogenExpansionState mol).toRawMolecule.bondOrder left right =
      mol.bondOrder left right := rfl

theorem getElem?_map_range {α : Type} (f : ℕ → α) (n idx : ℕ) (lt : idx < n) :
    ((List.range n).map f)[idx]? = some (f idx) := by
  rw [List.getElem?_eq_getElem (by simp [lt])]
  simp

@[simp] theorem initialHydrogenExpansionState_writtenNeighbors
    (mol : RawMolecule) (idx : ℕ) (lt : idx < mol.atomCount) :
    (initialHydrogenExpansionState mol).toRawMolecule.writtenNeighbors idx =
      mol.writtenNeighbors idx := by
  unfold initialHydrogenExpansionState HydrogenExpansionState.toRawMolecule writtenNeighbors
  rw [getElem?_map_range _ _ _ lt]

/-- Reifying the initial total order table preserves the complete checked intake contract. -/
theorem initialHydrogenExpansionState_stereochemicalAdmissible
    (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible) :
    (initialHydrogenExpansionState mol).toRawMolecule.StereochemicalAdmissible := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro bond member
      simpa [BondEndpointsOK] using admitted.1.1 bond member
    · simpa [BondRecordsUnique, initialHydrogenExpansionState,
        HydrogenExpansionState.toRawMolecule] using admitted.1.2
  · apply WrittenNeighborExact.of_at
    intro center
    have centerLt : center.val < mol.atomCount := by
      simpa using center.isLt
    let originalCenter : Fin mol.atomCount := ⟨center.val, centerLt⟩
    have original := WrittenNeighborExact.at mol admitted.2 originalCenter
    refine ⟨by simpa only [initialHydrogenExpansionState_writtenNeighbors _ _ centerLt]
      using original.1, ?_, ?_⟩
    · intro ligand member
      have originalMember : ligand ∈ mol.writtenNeighbors originalCenter.val := by
        simpa only [initialHydrogenExpansionState_writtenNeighbors _ _ centerLt] using member
      simpa using original.2.1 ligand originalMember
    · intro ligand
      have ligandLt : ligand.val < mol.atomCount := by simpa using ligand.isLt
      let originalLigand : Fin mol.atomCount := ⟨ligand.val, ligandLt⟩
      simpa only [initialHydrogenExpansionState_writtenNeighbors _ _ centerLt,
        initialHydrogenExpansionState_bondOrder] using original.2.2 originalLigand

/-- Index/row shape maintained by the expansion fold. -/
structure HydrogenExpansionState.ShapeInvariant
    (mol : RawMolecule) (state : HydrogenExpansionState) : Prop where
  fullOrder : state.2.2.length = state.1.length
  originalAtoms : mol.atomCount ≤ state.1.length

/-- Atom/valence shape of a hydrogen-expansion accumulator. Original atoms retain all source
metadata except the consumed inline-H count; every appended atom is an ordinary hydrogen with
exactly one incident single bond. -/
structure HydrogenExpansionState.MaterializedValenceInvariant
    (mol : RawMolecule) (state : HydrogenExpansionState) : Prop where
  originalAtom : ∀ index spec, mol.atomAt? index = some spec →
    state.toRawMolecule.atomAt? index = some (materializedAtomSpec spec)
  freshAtom : ∀ index atom, mol.atomCount ≤ index →
    state.toRawMolecule.atomAt? index = some atom →
      atom = AtomSpec.aliphatic Element.H ∧
        state.toRawMolecule.incidentBondOrderSum index = 1

theorem initialHydrogenExpansionState_shapeInvariant (mol : RawMolecule) :
    (initialHydrogenExpansionState mol).ShapeInvariant mol := by
  constructor <;> simp [initialHydrogenExpansionState, atomCount]

theorem initialHydrogenExpansionState_materializedValenceInvariant (mol : RawMolecule) :
    (initialHydrogenExpansionState mol).MaterializedValenceInvariant mol := by
  constructor
  · intro index spec lookup
    have sourceLookup : listGet? mol.atoms index = some spec := by
      simpa [atomAt?] using lookup
    unfold initialHydrogenExpansionState HydrogenExpansionState.toRawMolecule atomAt?
    rw [listGet?_map, sourceLookup]
    rfl
  · intro index atom lower lookup
    have upper : index < (mol.atoms.map materializedAtomSpec).length :=
      listGet?_eq_some_implies_lt _ _ _ (by
        simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule,
          atomAt?] using lookup)
    simp only [List.length_map] at upper
    exact (Nat.not_le_of_gt upper lower).elim

/-- One atom-index step of hydrogen materialization, named separately so preservation theorems can
reason about the exact production transformation. -/
def withExplicitHydrogensStep (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ) :
    HydrogenExpansionState :=
  let count := mol.hydrogenCountAt idx
  if count == 0 then state
  else
    let base := state.1.length
    let newAtoms := List.replicate count (AtomSpec.aliphatic Element.H)
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds :=
      hydrogenIds.map fun target =>
        { source := idx, target := target, kind := ParsedBondKind.single : RawBond }
    let hasPreceding := mol.hydrogenHasPreceding idx
    let baseOrder := state.2.2
    let updated :=
      (baseOrder.set idx
        (insertHydrogenInOrder (baseOrder.getD idx []) hasPreceding hydrogenIds))
        ++ hydrogenIds.map (fun _hydrogen => [idx])
    (state.1 ++ newAtoms, spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?) state.2.1 idx newBonds, updated)

theorem withExplicitHydrogensStep_preserves_shapeInvariant
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (valid : state.ShapeInvariant mol) :
    (withExplicitHydrogensStep mol state idx).ShapeInvariant mol := by
  simp only [withExplicitHydrogensStep]
  split
  · exact valid
  · constructor
    · simp [valid.fullOrder]
    · simpa using Nat.le_add_right_of_le valid.originalAtoms

theorem fold_withExplicitHydrogensStep_preserves_shapeInvariant
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (valid : state.ShapeInvariant mol) :
    (indices.foldl (withExplicitHydrogensStep mol) state).ShapeInvariant mol := by
  induction indices generalizing state with
  | nil => exact valid
  | cons idx rest ih =>
      exact ih _ (withExplicitHydrogensStep_preserves_shapeInvariant mol state idx valid)

/-- Bond-order contribution of one bond at a fixed atom. -/
def incidentContributionAt (atom : ℕ) (bond : RawBond) : ℕ :=
  if bond.source == atom || bond.target == atom then bond.kind.order else 0

private theorem foldl_incidentContributionAt
    (atom : ℕ) (bonds : List RawBond) (total : ℕ) :
    bonds.foldl
        (fun accumulated bond =>
          if bond.source == atom || bond.target == atom then
            accumulated + bond.kind.order
          else accumulated)
        total =
      total + (bonds.map (incidentContributionAt atom)).sum := by
  induction bonds generalizing total with
  | nil => simp
  | cons bond rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      unfold incidentContributionAt
      split <;> simp_all [Nat.add_assoc]

theorem incidentBondOrderSum_eq_incidentContributionAt_sum
    (mol : RawMolecule) (atom : ℕ) :
    mol.incidentBondOrderSum atom =
      (mol.bonds.map (incidentContributionAt atom)).sum := by
  unfold incidentBondOrderSum
  rw [foldl_incidentContributionAt]
  simp

/-- At an original atom, one materialization step adds exactly the target atom's fresh single-bond
hydrogen count and cannot alter any other original atom's used bond order. -/
theorem withExplicitHydrogensStep_incidentBondOrderSum_of_lt
    (mol : RawMolecule) (state : HydrogenExpansionState) (index target : ℕ)
    (targetLessState : target < state.1.length) :
    (withExplicitHydrogensStep mol state index).toRawMolecule.incidentBondOrderSum target =
      state.toRawMolecule.incidentBondOrderSum target +
        if index = target then mol.hydrogenCountAt index else 0 := by
  by_cases zero : mol.hydrogenCountAt index == 0
  · have countZero : mol.hydrogenCountAt index = 0 := by simpa using zero
    simp [withExplicitHydrogensStep, countZero]
  · let count := mol.hydrogenCountAt index
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun hydrogen =>
      { source := index, target := hydrogen, kind := ParsedBondKind.single : RawBond }
    have targetLessBase : target < base := targetLessState
    have permuted :
        (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[index]?) state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    rw [incidentBondOrderSum_eq_incidentContributionAt_sum,
      incidentBondOrderSum_eq_incidentContributionAt_sum]
    simp only [withExplicitHydrogensStep, if_neg zero,
      HydrogenExpansionState.toRawMolecule]
    change ((spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[index]?) state.2.1 index newBonds).map
      (incidentContributionAt target)).sum = _
    rw [(permuted.map (incidentContributionAt target)).sum_eq,
      List.map_append, List.sum_append]
    change (state.2.1.map (incidentContributionAt target)).sum +
        (newBonds.map (incidentContributionAt target)).sum = _
    by_cases same : index = target
    · subst index
      rw [if_pos rfl]
      simp only [newBonds, hydrogenIds, List.map_map]
      change (state.2.1.map (incidentContributionAt target)).sum +
          ((List.range count).map fun offset =>
            incidentContributionAt target
              { source := target, target := base + offset, kind := .single }).sum =
        (state.2.1.map (incidentContributionAt target)).sum + count
      simp [incidentContributionAt, ParsedBondKind.order]
    · have targetNotFresh : ∀ offset ∈ List.range count, base + offset ≠ target := by
        intro offset _member equal
        omega
      rw [if_neg same]
      simp only [newBonds, hydrogenIds, List.map_map]
      change (state.2.1.map (incidentContributionAt target)).sum +
          ((List.range count).map fun offset =>
            incidentContributionAt target
              { source := index, target := base + offset, kind := .single }).sum =
        (state.2.1.map (incidentContributionAt target)).sum
      have contributionsZero :
          ((List.range count).map fun offset =>
            incidentContributionAt target
              { source := index, target := base + offset, kind := .single }) =
            (List.range count).map (fun _offset => 0) := by
        apply List.map_congr_left
        intro offset member
        simp [incidentContributionAt, same, targetNotFresh offset member]
      rw [contributionsZero]
      simp

theorem withExplicitHydrogensStep_incidentBondOrderSum
    (mol : RawMolecule) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant mol) (index target : ℕ)
    (_indexBound : index < mol.atomCount) (targetBound : target < mol.atomCount) :
    (withExplicitHydrogensStep mol state index).toRawMolecule.incidentBondOrderSum target =
      state.toRawMolecule.incidentBondOrderSum target +
        if index = target then mol.hydrogenCountAt index else 0 := by
  exact withExplicitHydrogensStep_incidentBondOrderSum_of_lt mol state index target
    (lt_of_lt_of_le targetBound shape.originalAtoms)

theorem fold_withExplicitHydrogensStep_incidentBondOrderSum
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant mol) (indicesNodup : indices.Nodup)
    (indicesBound : ∀ index ∈ indices, index < mol.atomCount)
    (target : ℕ) (targetBound : target < mol.atomCount) :
    (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.incidentBondOrderSum
        target =
      state.toRawMolecule.incidentBondOrderSum target +
        if target ∈ indices then mol.hydrogenCountAt target else 0 := by
  induction indices generalizing state with
  | nil => simp
  | cons index rest inductionHypothesis =>
      have indexBound : index < mol.atomCount := indicesBound index (by simp)
      have restBound : ∀ item ∈ rest, item < mol.atomCount := by
        intro item present
        exact indicesBound item (by simp [present])
      have separated : index ∉ rest := (List.nodup_cons.mp indicesNodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp indicesNodup).2
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant mol state index shape
      rw [List.foldl_cons,
        inductionHypothesis (withExplicitHydrogensStep mol state index)
          nextShape restNodup restBound]
      rw [withExplicitHydrogensStep_incidentBondOrderSum
        mol state shape index target indexBound targetBound]
      by_cases same : index = target
      · subst index
        simp [separated]
      · by_cases targetInRest : target ∈ rest
        · simp [same, Ne.symm same, targetInRest]
        · simp [same, Ne.symm same, targetInRest]

theorem completeHydrogenExpansion_incidentBondOrderSum
    (mol : RawMolecule) (target : ℕ) (targetBound : target < mol.atomCount) :
    ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.incidentBondOrderSum target =
      mol.incidentBondOrderSum target + mol.hydrogenCountAt target := by
  rw [fold_withExplicitHydrogensStep_incidentBondOrderSum mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (initialHydrogenExpansionState_shapeInvariant mol) List.nodup_range
    (by intro index present; exact List.mem_range.mp present) target targetBound]
  have initialSum :
      (initialHydrogenExpansionState mol).toRawMolecule.incidentBondOrderSum target =
        mol.incidentBondOrderSum target := rfl
  rw [initialSum]
  simp [targetBound]

private theorem sum_beq_indicator_eq_count (values : List ℕ) (selected : ℕ) :
    (values.map fun value => if value == selected then 1 else 0).sum =
      values.count selected := by
  induction values with
  | nil => simp
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.count_cons]
      rw [inductionHypothesis]
      by_cases equal : value = selected <;> simp [equal, Nat.add_comm]

/-- Every atom freshly appended by one step has exactly its one new single bond and no old bond can
mention its out-of-range-before-the-step index. -/
theorem withExplicitHydrogensStep_fresh_incidentBondOrderSum
    (mol : RawMolecule) (state : HydrogenExpansionState) (index hydrogen : ℕ)
    (indexBound : index < mol.atomCount)
    (shape : state.ShapeInvariant mol) (well : state.toRawMolecule.WellFormed)
    (member : hydrogen ∈
      (List.range (mol.hydrogenCountAt index)).map fun offset => state.1.length + offset) :
    (withExplicitHydrogensStep mol state index).toRawMolecule.incidentBondOrderSum hydrogen = 1 := by
  let count := mol.hydrogenCountAt index
  let base := state.1.length
  let hydrogenIds := (List.range count).map fun offset => base + offset
  let newBonds := hydrogenIds.map fun fresh =>
    { source := index, target := fresh, kind := ParsedBondKind.single : RawBond }
  have hydrogenMember : hydrogen ∈ hydrogenIds := by simpa [hydrogenIds, count, base] using member
  have hydrogenBounds := freshHydrogenId_bounds base count hydrogen hydrogenMember
  have indexLessBase : index < base := lt_of_lt_of_le indexBound shape.originalAtoms
  have indexNeHydrogen : index ≠ hydrogen := Nat.ne_of_lt (lt_of_lt_of_le indexLessBase hydrogenBounds.1)
  have countNonzero : ¬(mol.hydrogenCountAt index == 0) = true := by
    intro zero
    have countZero : count = 0 := by simpa [count] using zero
    omega
  have permuted :
      (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[index]?) state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
    spliceHydrogenBondsWithPredecessor_perm _ _ _ _
  rw [incidentBondOrderSum_eq_incidentContributionAt_sum]
  simp only [withExplicitHydrogensStep, if_neg countNonzero,
    HydrogenExpansionState.toRawMolecule]
  change ((spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[index]?) state.2.1 index newBonds).map
    (incidentContributionAt hydrogen)).sum = 1
  rw [(permuted.map (incidentContributionAt hydrogen)).sum_eq,
    List.map_append, List.sum_append]
  have oldContributionsZero :
      state.2.1.map (incidentContributionAt hydrogen) = state.2.1.map (fun _bond => 0) := by
    apply List.map_congr_left
    intro bond bondMember
    have endpoints := well bond bondMember
    have sourceNe : bond.source ≠ hydrogen := by
      have sourceLt : bond.source < base := by
        simpa [HydrogenExpansionState.toRawMolecule, atomCount] using endpoints.1
      omega
    have targetNe : bond.target ≠ hydrogen := by
      have targetLt : bond.target < base := by
        simpa [HydrogenExpansionState.toRawMolecule, atomCount] using endpoints.2.1
      omega
    simp [incidentContributionAt, sourceNe, targetNe]
  rw [oldContributionsZero]
  simp
  have freshContributions :
      newBonds.map (incidentContributionAt hydrogen) =
        hydrogenIds.map (fun fresh => if fresh == hydrogen then 1 else 0) := by
    simp only [newBonds, List.map_map]
    apply List.map_congr_left
    intro fresh _freshMember
    simp [incidentContributionAt, indexNeHydrogen, ParsedBondKind.order]
  rw [freshContributions, sum_beq_indicator_eq_count]
  have hydrogenIdsNodup : hydrogenIds.Nodup := by
    simpa [hydrogenIds] using freshHydrogenIds_nodup base count
  exact List.count_eq_one_of_mem hydrogenIdsNodup hydrogenMember

theorem withExplicitHydrogensStep_preserves_materializedValenceInvariant
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (indexBound : index < mol.atomCount) (shape : state.ShapeInvariant mol)
    (well : state.toRawMolecule.WellFormed)
    (invariant : state.MaterializedValenceInvariant mol) :
    (withExplicitHydrogensStep mol state index).MaterializedValenceInvariant mol := by
  by_cases zero : (mol.hydrogenCountAt index == 0) = true
  · simpa [withExplicitHydrogensStep, zero] using invariant
  · let count := mol.hydrogenCountAt index
    let base := state.1.length
    constructor
    · intro originalIndex spec sourceLookup
      have originalBound : originalIndex < mol.atomCount :=
        listGet?_eq_some_implies_lt mol.atoms originalIndex spec (by
          simpa [atomAt?] using sourceLookup)
      have stateBound : originalIndex < state.1.length :=
        lt_of_lt_of_le originalBound shape.originalAtoms
      have stateLookup := invariant.originalAtom originalIndex spec sourceLookup
      simp only [withExplicitHydrogensStep, if_neg zero,
        HydrogenExpansionState.toRawMolecule, atomAt?]
      rw [listGet?_append_left_of_lt state.1
        (List.replicate count (AtomSpec.aliphatic Element.H)) originalIndex stateBound]
      simpa [HydrogenExpansionState.toRawMolecule, atomAt?] using stateLookup
    · intro atomIndex atom originalCountLe lookup
      have expandedLookup :
          listGet? (state.1 ++ List.replicate count (AtomSpec.aliphatic Element.H))
            atomIndex = some atom := by
        simpa [withExplicitHydrogensStep, zero, count,
          HydrogenExpansionState.toRawMolecule, atomAt?] using lookup
      by_cases old : atomIndex < state.1.length
      · have stateLookup : state.toRawMolecule.atomAt? atomIndex = some atom := by
          unfold HydrogenExpansionState.toRawMolecule atomAt?
          rw [← listGet?_append_left_of_lt state.1
            (List.replicate count (AtomSpec.aliphatic Element.H)) atomIndex old]
          exact expandedLookup
        obtain ⟨atomIdentity, oldIncident⟩ :=
          invariant.freshAtom atomIndex atom originalCountLe stateLookup
        refine ⟨atomIdentity, ?_⟩
        rw [withExplicitHydrogensStep_incidentBondOrderSum_of_lt mol state index atomIndex old]
        have distinct : index ≠ atomIndex := by omega
        simp [distinct, oldIncident]
      · have baseLe : state.1.length ≤ atomIndex := Nat.le_of_not_gt old
        have appendedLookup :
            listGet? (List.replicate count (AtomSpec.aliphatic Element.H))
              (atomIndex - state.1.length) = some atom := by
          rw [← listGet?_append_right_of_length_le state.1
            (List.replicate count (AtomSpec.aliphatic Element.H)) atomIndex baseLe]
          exact expandedLookup
        have atomMember : atom ∈ List.replicate count (AtomSpec.aliphatic Element.H) :=
          listGet?_eq_some_implies_mem _ _ _ appendedLookup
        have atomIdentity : atom = AtomSpec.aliphatic Element.H :=
          (List.mem_replicate.mp atomMember).2
        have expandedBound : atomIndex < state.1.length + count := by
          have lookupBound := listGet?_eq_some_implies_lt _ _ _ expandedLookup
          simpa using lookupBound
        have freshMember : atomIndex ∈
            (List.range (mol.hydrogenCountAt index)).map
              (fun offset => state.1.length + offset) := by
          apply List.mem_map.mpr
          refine ⟨atomIndex - state.1.length, List.mem_range.mpr ?_, ?_⟩
          · omega
          · omega
        refine ⟨atomIdentity, ?_⟩
        exact withExplicitHydrogensStep_fresh_incidentBondOrderSum
          mol state index atomIndex indexBound shape well freshMember

theorem withExplicitHydrogensStep_preserves_wellFormed
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (valid : state.ShapeInvariant mol) (idxBound : idx < mol.atomCount)
    (well : state.toRawMolecule.WellFormed) :
    (withExplicitHydrogensStep mol state idx).toRawMolecule.WellFormed := by
  simp only [withExplicitHydrogensStep]
  split
  · exact well
  · dsimp only [HydrogenExpansionState.toRawMolecule]
    intro bond member
    let count := mol.hydrogenCountAt idx
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun target =>
      { source := idx, target := target, kind := ParsedBondKind.single : RawBond }
    have permuted :
        (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?) state.2.1 idx newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    have appended : bond ∈ state.2.1 ++ newBonds := permuted.mem_iff.mp member
    unfold BondEndpointsOK atomCount
    simp only [List.length_append, List.length_replicate]
    change bond.source < base + count ∧ bond.target < base + count ∧
      bond.source ≠ bond.target
    rcases List.mem_append.mp appended with old | fresh
    · have endpoints := well bond old
      exact ⟨lt_of_lt_of_le endpoints.1 (Nat.le_add_right _ _),
        lt_of_lt_of_le endpoints.2.1 (Nat.le_add_right _ _), endpoints.2.2⟩
    · rcases List.mem_map.mp fresh with ⟨hydrogen, hydrogenMember, rfl⟩
      have bounds := freshHydrogenId_bounds base count hydrogen hydrogenMember
      have idxOld : idx < base := lt_of_lt_of_le idxBound valid.originalAtoms
      exact ⟨lt_of_lt_of_le idxOld (Nat.le_add_right _ _), bounds.2,
        Nat.ne_of_lt (lt_of_lt_of_le idxOld bounds.1)⟩

theorem fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (indicesBound : ∀ index ∈ indices, index < mol.atomCount)
    (shape : state.ShapeInvariant mol) (well : state.toRawMolecule.WellFormed)
    (invariant : state.MaterializedValenceInvariant mol) :
    (indices.foldl (withExplicitHydrogensStep mol) state).MaterializedValenceInvariant mol := by
  induction indices generalizing state with
  | nil => exact invariant
  | cons index rest inductionHypothesis =>
      have indexBound : index < mol.atomCount := indicesBound index (by simp)
      have restBound : ∀ item ∈ rest, item < mol.atomCount := by
        intro item present
        exact indicesBound item (by simp [present])
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant mol state index shape
      have nextWell :=
        withExplicitHydrogensStep_preserves_wellFormed mol state index shape indexBound well
      have nextInvariant :=
        withExplicitHydrogensStep_preserves_materializedValenceInvariant
          mol state index indexBound shape well invariant
      exact inductionHypothesis (withExplicitHydrogensStep mol state index)
        restBound nextShape nextWell nextInvariant

theorem withExplicitHydrogensStep_preserves_bondRecordsUnique
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (valid : state.ShapeInvariant mol) (idxBound : idx < mol.atomCount)
    (well : state.toRawMolecule.WellFormed)
    (unique : state.toRawMolecule.BondRecordsUnique) :
    (withExplicitHydrogensStep mol state idx).toRawMolecule.BondRecordsUnique := by
  simp only [withExplicitHydrogensStep]
  split
  · exact unique
  · dsimp only [HydrogenExpansionState.toRawMolecule]
    let count := mol.hydrogenCountAt idx
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun target =>
      { source := idx, target := target, kind := ParsedBondKind.single : RawBond }
    have idxOld : idx < base := lt_of_lt_of_le idxBound valid.originalAtoms
    have permuted :
        (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?) state.2.1 idx newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    unfold BondRecordsUnique
    have keyPermuted := permuted.map RawBond.edgeKey
    rw [keyPermuted.nodup_iff]
    rw [List.map_append, List.nodup_append]
    refine ⟨unique, ?_, ?_⟩
    · have idsNodup : hydrogenIds.Nodup := freshHydrogenIds_nodup base count
      rw [show newBonds.map RawBond.edgeKey =
          hydrogenIds.map (fun hydrogen => (idx, hydrogen)) by
        simp only [newBonds, List.map_map]
        apply List.map_congr_left
        intro hydrogen hydrogenMember
        have bounds := freshHydrogenId_bounds base count hydrogen hydrogenMember
        simp [RawBond.edgeKey,
          Nat.min_eq_left (Nat.le_of_lt (lt_of_lt_of_le idxOld bounds.1)),
          Nat.max_eq_right (Nat.le_of_lt (lt_of_lt_of_le idxOld bounds.1))]]
      exact idsNodup.map (by
        intro first second equal
        exact congrArg Prod.snd equal)
    · intro oldKey oldKeyMember newKey newKeyMember equal
      rcases List.mem_map.mp oldKeyMember with ⟨oldBond, oldBondMember, rfl⟩
      rcases List.mem_map.mp newKeyMember with ⟨newBond, newBondMember, rfl⟩
      rcases List.mem_map.mp newBondMember with ⟨hydrogen, hydrogenMember, rfl⟩
      have oldEndpoints := well oldBond oldBondMember
      have hydrogenBounds := freshHydrogenId_bounds base count hydrogen hydrogenMember
      have oldMaxLt : max oldBond.source oldBond.target < base :=
        max_lt oldEndpoints.1 oldEndpoints.2.1
      have newMaxEq : max idx hydrogen = hydrogen :=
        Nat.max_eq_right (Nat.le_of_lt (lt_of_lt_of_le idxOld hydrogenBounds.1))
      have secondEqual := congrArg Prod.snd equal
      simp only [RawBond.edgeKey, newMaxEq] at secondEqual
      omega

theorem withExplicitHydrogensStep_preserves_admissible
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (valid : state.ShapeInvariant mol) (idxBound : idx < mol.atomCount)
    (admitted : state.toRawMolecule.Admissible) :
    (withExplicitHydrogensStep mol state idx).toRawMolecule.Admissible :=
  ⟨withExplicitHydrogensStep_preserves_wellFormed mol state idx valid idxBound admitted.1,
    withExplicitHydrogensStep_preserves_bondRecordsUnique mol state idx valid idxBound
      admitted.1 admitted.2⟩

theorem fold_withExplicitHydrogensStep_preserves_admissible
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (indicesBound : ∀ idx ∈ indices, idx < mol.atomCount)
    (shape : state.ShapeInvariant mol)
    (admitted : state.toRawMolecule.Admissible) :
    (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.Admissible := by
  induction indices generalizing state with
  | nil => exact admitted
  | cons idx rest ih =>
      have idxBound : idx < mol.atomCount := indicesBound idx (by simp)
      have restBound : ∀ atom ∈ rest, atom < mol.atomCount := by
        intro atom atomMem
        exact indicesBound atom (by simp [atomMem])
      have nextAdmitted :=
        withExplicitHydrogensStep_preserves_admissible mol state idx shape idxBound admitted
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant mol state idx shape
      exact ih (withExplicitHydrogensStep mol state idx) restBound nextShape nextAdmitted

/-- Every standard fill valence is bounded by an admitted validation valence for the same atom.
The aromatic-nitrogen case is deliberately an inequality: its no-added-H fill value is two while
the validation table's supported aromatic valence is three. -/
theorem defaultValence_supported (atom : AtomSpec) (target : ℕ)
    (member : target ∈ defaultValences atom) :
    ∃ allowed, allowed ∈ atom.allowedValences ∧ target ≤ allowed := by
  by_cases aromatic : atom.aromatic = true
  · cases element : atom.element <;>
      simp_all [defaultValences, elementDefaultValences, AtomSpec.allowedValences,
        Element.allowedValences] <;> omega
  · have nonaromatic : atom.aromatic = false := Bool.eq_false_of_not_eq_true aromatic
    cases element : atom.element <;>
      by_cases negative : atom.charge < 0 <;>
        simp_all [defaultValences, elementDefaultValences, AtomSpec.allowedValences,
          Element.allowedValences] <;> try split <;> simp_all
    all_goals rcases member with rfl | rfl | rfl <;> simp

/-- The hydrogen count chosen by the OpenSMILES policy always fits an allowed valence whenever the
source atom itself passed the valence table. -/
theorem incidentBondOrderSum_add_hydrogenCountAt_supported
    (mol : RawMolecule) (valence : mol.ValenceOK) (index : ℕ) (atom : AtomSpec)
    (lookup : mol.atomAt? index = some atom) :
    ∃ allowed, allowed ∈ atom.allowedValences ∧
      mol.incidentBondOrderSum index + mol.hydrogenCountAt index ≤ allowed := by
  obtain ⟨allowed, allowedMember, sourceBound⟩ := valence index atom lookup
  cases exactHydrogens : atom.explicitHydrogens? with
  | some count =>
      refine ⟨allowed, allowedMember, ?_⟩
      have sourceUsed : mol.usedValenceAt index = count + mol.incidentBondOrderSum index := by
        simp [usedValenceAt, lookup, AtomSpec.explicitHydrogens, exactHydrogens]
      have hydrogenCount : mol.hydrogenCountAt index = count := by
        simp [hydrogenCountAt, lookup, exactHydrogens]
      rw [hydrogenCount, Nat.add_comm]
      simpa [sourceUsed] using sourceBound
  | none =>
      have sourceUsed : mol.usedValenceAt index = mol.incidentBondOrderSum index := by
        simp [usedValenceAt, lookup, AtomSpec.explicitHydrogens, exactHydrogens]
      rw [sourceUsed] at sourceBound
      cases found : (defaultValences atom).find?
          (fun target => mol.incidentBondOrderSum index ≤ target) with
      | none =>
          refine ⟨allowed, allowedMember, ?_⟩
          simp [hydrogenCountAt, lookup, exactHydrogens, found, sourceBound]
      | some target =>
          obtain ⟨supported, supportedMember, targetBound⟩ :=
            defaultValence_supported atom target (List.mem_of_find?_eq_some found)
          refine ⟨supported, supportedMember, ?_⟩
          have usedBound : mol.incidentBondOrderSum index ≤ target := by
            exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
          simp [hydrogenCountAt, lookup, exactHydrogens, found]
          omega

/-- Materialise every implied hydrogen as a parsed atom, preserving OpenSMILES neighbour order. -/
def withExplicitHydrogens (mol : RawMolecule) : RawMolecule :=
  let result :=
    (List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
      (initialHydrogenExpansionState mol)
  { result.toRawMolecule.withExactWrittenNeighbors with
      introductionPredecessors := mol.introductionPredecessors }

/-- Hydrogen expansion preserves the source-token provenance prefix exactly. No provenance is
invented for generated hydrogen atoms, which did not occur as atom tokens in the input. -/
@[simp] theorem withExplicitHydrogens_introductionPredecessors (mol : RawMolecule) :
    mol.withExplicitHydrogens.introductionPredecessors = mol.introductionPredecessors := rfl

@[simp] theorem withExplicitHydrogens_introductionPredecessor_at
    (mol : RawMolecule) (idx : ℕ) :
    mol.withExplicitHydrogens.introductionPredecessors[idx]? =
      mol.introductionPredecessors[idx]? := rfl

/-- Materializing inline/implied hydrogens preserves the validation valence contract on every
well-formed source molecule. Inline counts are consumed exactly once, original atoms receive the
computed number of single bonds, and each appended hydrogen has used valence one. -/
theorem withExplicitHydrogens_preserves_valenceOK (mol : RawMolecule)
    (well : mol.WellFormed) (valence : mol.ValenceOK) :
    mol.withExplicitHydrogens.ValenceOK := by
  let result :=
    (List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
      (initialHydrogenExpansionState mol)
  have initialWell : (initialHydrogenExpansionState mol).toRawMolecule.WellFormed := by
    intro bond member
    simpa [BondEndpointsOK] using well bond member
  have invariant : result.MaterializedValenceInvariant mol := by
    exact fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant mol
      (List.range mol.atomCount) (initialHydrogenExpansionState mol)
      (by intro index member; exact List.mem_range.mp member)
      (initialHydrogenExpansionState_shapeInvariant mol) initialWell
      (initialHydrogenExpansionState_materializedValenceInvariant mol)
  intro index atom expandedLookup
  have resultLookup : result.toRawMolecule.atomAt? index = some atom := by
    simpa [withExplicitHydrogens, result, withExactWrittenNeighbors, atomAt?] using expandedLookup
  change ∃ allowed, allowed ∈ atom.allowedValences ∧
    result.toRawMolecule.usedValenceAt index ≤ allowed
  by_cases originalBound : index < mol.atomCount
  · obtain ⟨source, sourceLookup⟩ := listGet?_exists_of_lt mol.atoms index originalBound
    have sourceLookupAt : mol.atomAt? index = some source := by
      simpa [atomAt?] using sourceLookup
    have materializedLookup := invariant.originalAtom index source sourceLookupAt
    have atomIdentity : atom = materializedAtomSpec source := by
      rw [resultLookup] at materializedLookup
      exact Option.some.inj materializedLookup
    subst atom
    obtain ⟨allowed, allowedMember, supported⟩ :=
      incidentBondOrderSum_add_hydrogenCountAt_supported
        mol valence index source sourceLookupAt
    refine ⟨allowed, by simpa using allowedMember, ?_⟩
    have incident := completeHydrogenExpansion_incidentBondOrderSum mol index originalBound
    simp only [usedValenceAt, resultLookup, materializedAtomSpec_explicitHydrogens,
      zero_add]
    rw [incident]
    exact supported
  · have originalCountLe : mol.atomCount ≤ index := Nat.le_of_not_gt originalBound
    obtain ⟨atomIdentity, incident⟩ :=
      invariant.freshAtom index atom originalCountLe resultLookup
    subst atom
    refine ⟨1, by simp [AtomSpec.aliphatic, AtomSpec.allowedValences,
      Element.allowedValences], ?_⟩
    simp only [usedValenceAt, resultLookup, AtomSpec.explicitHydrogens,
      AtomSpec.aliphatic]
    rw [incident]
    simp

/-- Materializing hydrogens universally preserves endpoint validity and unordered-edge
uniqueness. The final exact-order canonicalizer leaves the molecular graph unchanged. -/
theorem withExplicitHydrogens_preserves_admissible (mol : RawMolecule)
    (admitted : mol.StereochemicalAdmissible) :
    mol.withExplicitHydrogens.Admissible := by
  unfold withExplicitHydrogens
  apply (withExactWrittenNeighbors_admissible_iff _).mpr
  exact fold_withExplicitHydrogensStep_preserves_admissible mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro idx member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol)
    (initialHydrogenExpansionState_stereochemicalAdmissible mol admitted).1

theorem withExplicitHydrogens_writtenNeighborExact (mol : RawMolecule) :
    mol.withExplicitHydrogens.WrittenNeighborExact := by
  unfold withExplicitHydrogens
  exact withExactWrittenNeighbors_writtenNeighborExact
    (((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
      (initialHydrogenExpansionState mol)).toRawMolecule)

/-- Hydrogen materialization now preserves the complete stereochemical admission boundary for
every admitted finite raw molecule. -/
theorem withExplicitHydrogens_preserves_stereochemicalAdmissible (mol : RawMolecule)
    (admitted : mol.StereochemicalAdmissible) :
    mol.withExplicitHydrogens.StereochemicalAdmissible :=
  ⟨mol.withExplicitHydrogens_preserves_admissible admitted,
    mol.withExplicitHydrogens_writtenNeighborExact⟩

/-- Rule-2 source coverage of the atom list inside a hydrogen-expansion accumulator. -/
def HydrogenExpansionState.Rule2MassesKnown (state : HydrogenExpansionState) : Prop :=
  ∀ atom, atom ∈ state.1 →
    ∃ mass, rule2MassPico? atom.element atom.isotope? = some mass

theorem initialHydrogenExpansionState_rule2MassesKnown
    (mol : RawMolecule) (known : mol.Rule2MassesKnown) :
    (initialHydrogenExpansionState mol).Rule2MassesKnown := by
  intro atom member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  simpa using known source sourceMember

theorem withExplicitHydrogensStep_preserves_rule2MassesKnown
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (known : state.Rule2MassesKnown) :
    (withExplicitHydrogensStep mol state idx).Rule2MassesKnown := by
  unfold withExplicitHydrogensStep
  by_cases zero : (mol.hydrogenCountAt idx == 0) = true
  · rw [if_pos zero]
    exact known
  · rw [if_neg zero]
    intro atom membership
    change atom ∈ state.1 ++
      List.replicate (mol.hydrogenCountAt idx) (AtomSpec.aliphatic Element.H) at membership
    rcases List.mem_append.mp membership with original | added
    · exact known atom original
    · have atomIdentity : atom = AtomSpec.aliphatic Element.H := by
        exact (List.mem_replicate.mp added).2
      subst atom
      exact ⟨1007825031898, by decide⟩

theorem fold_withExplicitHydrogensStep_preserves_rule2MassesKnown
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (known : state.Rule2MassesKnown) :
    (indices.foldl (withExplicitHydrogensStep mol) state).Rule2MassesKnown := by
  induction indices generalizing state with
  | nil => exact known
  | cons idx rest inductionHypothesis =>
      exact inductionHypothesis (withExplicitHydrogensStep mol state idx)
        (withExplicitHydrogensStep_preserves_rule2MassesKnown mol state idx known)

/-- Adding implicit ordinary hydrogens cannot introduce an unknown Rule-2 datum. -/
theorem withExplicitHydrogens_preserves_rule2MassesKnown (mol : RawMolecule)
    (known : mol.Rule2MassesKnown) : mol.withExplicitHydrogens.Rule2MassesKnown := by
  unfold withExplicitHydrogens RawMolecule.Rule2MassesKnown
  exact fold_withExplicitHydrogensStep_preserves_rule2MassesKnown mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (initialHydrogenExpansionState_rule2MassesKnown mol known)

theorem withExplicitHydrogens_rule2MassesKnown?_eq_true (mol : RawMolecule)
    (known : mol.rule2MassesKnown? = true) :
    mol.withExplicitHydrogens.rule2MassesKnown? = true := by
  apply (mol.withExplicitHydrogens.rule2MassesKnown?_eq_true_iff).mpr
  exact mol.withExplicitHydrogens_preserves_rule2MassesKnown
    ((mol.rule2MassesKnown?_eq_true_iff).mp known)

end RawMolecule

namespace CertifiedChemistryNormalizationResult

/-- The exact molecule consumed by branch ranking retains a Rule-2 source certificate after all
implicit hydrogens have been materialized. -/
theorem expandedRule2MassesKnown (certified : CertifiedChemistryNormalizationResult) :
    certified.result.parsed.withExplicitHydrogens.Rule2MassesKnown :=
  certified.result.parsed.withExplicitHydrogens_preserves_rule2MassesKnown
    certified.rule2MassesKnown

theorem expandedRule2MassesKnown?_eq_true (certified : CertifiedChemistryNormalizationResult) :
    certified.result.parsed.withExplicitHydrogens.rule2MassesKnown? = true :=
  (certified.result.parsed.withExplicitHydrogens.rule2MassesKnown?_eq_true_iff).mpr
    certified.expandedRule2MassesKnown

end CertifiedChemistryNormalizationResult

namespace ChemistryNormalizationResult

/-- Executable structural admission for the exact hydrogen-expanded molecule consumed by CIP
branch discovery and ranking. -/
def expandedStereochemicalAdmissible?
    (result : ChemistryNormalizationResult) : Bool :=
  result.parsed.withExplicitHydrogens.stereochemicalAdmissible?

/-- Proposition reflected by `expandedStereochemicalAdmissible?`. -/
def ExpandedStereochemicalAdmissible
    (result : ChemistryNormalizationResult) : Prop :=
  result.parsed.withExplicitHydrogens.StereochemicalAdmissible

@[simp] theorem expandedStereochemicalAdmissible?_eq_true_iff
    (result : ChemistryNormalizationResult) :
    result.expandedStereochemicalAdmissible? = true ↔
      result.ExpandedStereochemicalAdmissible := by
  exact result.parsed.withExplicitHydrogens.stereochemicalAdmissible?_eq_true_iff

end ChemistryNormalizationResult

end OneCenter
end TetraStereo
