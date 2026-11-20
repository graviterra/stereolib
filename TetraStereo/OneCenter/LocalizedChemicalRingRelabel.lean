import TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Relabelling transport of the canonical expansion under a molecular symmetry

A structural symmetry `σ` is a bijective relabelling of raw atom identifiers that preserves
bond orders and the written ligand multiset, and fixes every identifier outside
the atom range (so the lone-pair phantom is fixed). This module proves that the actual canonical
expansion used by the recursive marked evaluator is covariant under `σ`:

* `children_map`: the canonical children of the relabelled occurrence are, up to order, the
  relabelled children (ring duplicates and their recorded distances included);
* `frameAtoms_map`: the four-ligand frame of the relabelled occurrence exists exactly when the
  original frame exists and is, up to order, the relabelled frame (phantom included);
* `reached_map`: reachability from an in-range centre is preserved;
* `readback_map`: the geometric readback of a relabelled priority list is the readback of the
  original list under the pulled-back geometry `geom ∘ σ`.

Order is preserved only up to permutation because the bond list is not required to be
`σ`-invariant as a list. No comparator, descriptor, geometry sense or chemical claim appears here;
this is the structural half of a symmetry argument about the actual evaluator, on arbitrary finite
single-bond molecules with rings. The older `Symmetry` additionally requires involutivity and
coerces to `StructuralSymmetry`; only the explicit two-application lemmas require that restriction.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingRelabel

open LocalizedGenericMarkedRecalculation LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## Molecular symmetries -/

/-- A bijective relabelling preserving bonds and the written ligand view up to permutation.
Parser atom records are not used by the structural recursion. The inverse may differ from
the original relabelling. -/
structure StructuralSymmetry (mol : RawMolecule) (σ : Nat → Nat) : Prop where
  bijective : Function.Bijective σ
  inRange : ∀ x, x < mol.atomCount → σ x < mol.atomCount
  outside : ∀ x, mol.atomCount ≤ x → σ x = x
  bonds : ∀ x y, mol.bondOrder (σ x) (σ y) = mol.bondOrder x y
  ligands : ∀ x, x < mol.atomCount →
    (mol.ligandsWithLonePair (σ x)).Perm ((mol.ligandsWithLonePair x).map σ)

namespace StructuralSymmetry

variable {mol : RawMolecule} {σ : Nat → Nat}

theorem injective (sym : StructuralSymmetry mol σ) : Function.Injective σ := sym.bijective.1

theorem surjective (sym : StructuralSymmetry mol σ) : Function.Surjective σ := sym.bijective.2

theorem phantom (sym : StructuralSymmetry mol σ) : σ mol.atomCount = mol.atomCount :=
  sym.outside mol.atomCount le_rfl

/-- An explicit inverse preserves the same structural domain. -/
theorem inverse (sym : StructuralSymmetry mol σ) (τ : Nat → Nat)
    (leftInv : Function.LeftInverse τ σ) (rightInv : Function.RightInverse τ σ) :
    StructuralSymmetry mol τ := by
  have range : ∀ x, x < mol.atomCount → τ x < mol.atomCount := by
    intro x hx
    by_contra bad
    have fixed := sym.outside (τ x) (Nat.le_of_not_gt bad)
    have same : τ x = x := fixed.symm.trans (rightInv x)
    exact bad (by rw [same]; exact hx)
  refine ⟨⟨rightInv.injective, fun x => ⟨σ x, leftInv x⟩⟩, range, ?_, ?_, ?_⟩
  · intro x hx
    have h := leftInv x
    rwa [sym.outside x hx] at h
  · intro x y
    have h := sym.bonds (τ x) (τ y)
    rw [rightInv x, rightInv y] at h
    exact h.symm
  · intro x hx
    have h := (sym.ligands (τ x) (range x hx)).map τ
    rw [rightInv x, List.map_map] at h
    have cancel : (mol.ligandsWithLonePair (τ x)).map (τ ∘ σ) =
        mol.ligandsWithLonePair (τ x) := by
      calc
        _ = (mol.ligandsWithLonePair (τ x)).map id :=
          List.map_congr_left fun a _ => leftInv a
        _ = _ := List.map_id _
    rw [cancel] at h
    exact h.symm

end StructuralSymmetry

/-- An involutive relabelling of atom identifiers that preserves the raw molecular constitution
and its written ligand view, and fixes every identifier outside the atom range. -/
structure Symmetry (mol : RawMolecule) (σ : Nat → Nat) : Prop where
  involutive : Function.Involutive σ
  inRange : ∀ x, x < mol.atomCount → σ x < mol.atomCount
  outside : ∀ x, mol.atomCount ≤ x → σ x = x
  atoms : ∀ x, x < mol.atomCount → mol.atomAt? (σ x) = mol.atomAt? x
  bonds : ∀ x y, mol.bondOrder (σ x) (σ y) = mol.bondOrder x y
  ligands : ∀ x, x < mol.atomCount →
    (mol.ligandsWithLonePair (σ x)).Perm ((mol.ligandsWithLonePair x).map σ)

namespace Symmetry

variable {mol : RawMolecule} {σ : Nat → Nat}

theorem injective (sym : Symmetry mol σ) : Function.Injective σ := sym.involutive.injective

theorem apply_apply (sym : Symmetry mol σ) (x : Nat) : σ (σ x) = x := sym.involutive x

theorem phantom (sym : Symmetry mol σ) : σ mol.atomCount = mol.atomCount :=
  sym.outside mol.atomCount le_rfl

theorem map_map (sym : Symmetry mol σ) (l : List Nat) : (l.map σ).map σ = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x _
  exact sym.apply_apply x

/-- Compatibility conversion: involutive symmetries are structural bijections. -/
def toStructuralSymmetry (sym : Symmetry mol σ) : StructuralSymmetry mol σ where
  bijective := ⟨sym.involutive.injective, sym.involutive.surjective⟩
  inRange := sym.inRange
  outside := sym.outside
  bonds := sym.bonds
  ligands := sym.ligands

end Symmetry

instance {mol : RawMolecule} {σ : Nat → Nat} :
    Coe (Symmetry mol σ) (StructuralSymmetry mol σ) := ⟨Symmetry.toStructuralSymmetry⟩

/-! ## Relabelled occurrences -/

/-- The relabelled occurrence: same provenance, relabelled atom, parent and history. -/
def mapNode (σ : Nat → Nat) (node : Node) : Node :=
  { atom := σ node.atom, parent := σ node.parent, history := node.history.map σ,
    provenance := node.provenance }

@[simp] theorem mapNode_atom (σ : Nat → Nat) (node : Node) : (mapNode σ node).atom = σ node.atom :=
  rfl
@[simp] theorem mapNode_parent (σ : Nat → Nat) (node : Node) :
    (mapNode σ node).parent = σ node.parent := rfl
@[simp] theorem mapNode_history (σ : Nat → Nat) (node : Node) :
    (mapNode σ node).history = node.history.map σ := rfl
@[simp] theorem mapNode_provenance (σ : Nat → Nat) (node : Node) :
    (mapNode σ node).provenance = node.provenance := rfl

theorem mapNode_forcedLeaf (σ : Nat → Nat) (node : Node) :
    (mapNode σ node).forcedLeaf = node.forcedLeaf := rfl

theorem mapNode_depth (σ : Nat → Nat) (node : Node) : (mapNode σ node).depth = node.depth := by
  simp [RawMolecule.CanonicalBranchNode.depth, mapNode]

theorem mapNode_mapNode {mol : RawMolecule} {σ : Nat → Nat} (sym : Symmetry mol σ) (node : Node) :
    mapNode σ (mapNode σ node) = node := by
  cases node
  simp [mapNode, sym.apply_apply, sym.map_map]

theorem mapNode_injective {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ) :
    Function.Injective (mapNode σ) := by
  intro a b h
  have atom := sym.injective (congrArg RawMolecule.CanonicalBranchNode.atom h)
  have parent := sym.injective (congrArg RawMolecule.CanonicalBranchNode.parent h)
  have history := sym.injective.list_map
    (congrArg RawMolecule.CanonicalBranchNode.history h)
  have provenance := congrArg RawMolecule.CanonicalBranchNode.provenance h
  cases a
  cases b
  simp_all only [mapNode_provenance]

theorem mapNode_canonicalCenterRoot (σ : Nat → Nat) (center : Nat) :
    mapNode σ (canonicalCenterRoot center) = canonicalCenterRoot (σ center) := rfl

theorem canonicalOriginalParent?_map (σ : Nat → Nat) (node : Node) :
    canonicalOriginalParent? (mapNode σ node) =
      (canonicalOriginalParent? node).map (mapNode σ) := by
  unfold canonicalOriginalParent?
  simp only [mapNode_history]
  rcases node.history with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> rfl

/-! ## Children -/

theorem firstNatIndex?_map {σ : Nat → Nat} (injective : Function.Injective σ) (target : Nat) :
    ∀ l : List Nat, RawMolecule.firstNatIndex? (σ target) (l.map σ) =
      RawMolecule.firstNatIndex? target l
  | [] => rfl
  | atom :: atoms => by
      simp only [List.map_cons, RawMolecule.firstNatIndex?, injective.eq_iff,
        firstNatIndex?_map injective target atoms]

theorem canonicalHistoryDistance_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (node : Node) (atom : Nat) :
    RawMolecule.canonicalHistoryDistance (mapNode σ node) (σ atom) =
      RawMolecule.canonicalHistoryDistance node atom := by
  unfold RawMolecule.canonicalHistoryDistance
  rw [mapNode_depth, mapNode_history, ← List.map_reverse, firstNatIndex?_map sym.injective]

theorem contains_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ) (l : List Nat)
    (atom : Nat) : (l.map σ).contains (σ atom) = l.contains atom := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, member, eq⟩
    rw [sym.injective eq] at member
    exact member
  · intro member
    exact ⟨atom, member, rfl⟩

/-- The single-bond canonical child at one neighbour atom. -/
def childOf (node : Node) (next : Nat) : Node :=
  { atom := next, parent := node.atom, history := next :: node.history,
    provenance :=
      if node.history.contains next then
        RawMolecule.CanonicalNodeProvenance.ringDuplicate
          (RawMolecule.canonicalHistoryDistance node next)
      else RawMolecule.CanonicalNodeProvenance.realAtom }

theorem childOf_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ) (node : Node)
    (next : Nat) : childOf (mapNode σ node) (σ next) = mapNode σ (childOf node next) := by
  unfold childOf
  rw [canonicalHistoryDistance_map sym, mapNode_history, contains_map sym]
  simp [mapNode]

/-- On single-bond molecules every canonical child is the child at a neighbour atom other than
the parent, in neighbour order. -/
theorem canonicalChildren_eq (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node : Node) (real : node.forcedLeaf = false) :
    mol.canonicalChildren node =
      ((mol.canonicalIncidentNeighbors node.atom).erase node.parent).map (childOf node) := by
  have copies := mol.canonicalChildCopies_eq_erase_seed node
  rw [RawMolecule.eraseCanonicalParentCopy_eq_erase, seeds_eq_neighbors mol wellFormed single]
    at copies
  have injective : Function.Injective (fun atom : Nat => (atom, (0 : Nat))) := by
    intro a b eq
    exact (Prod.mk.inj eq).1
  rw [← List.map_erase injective] at copies
  unfold RawMolecule.canonicalChildren
  rw [if_neg (by simp [real]), copies, List.map_map]
  apply List.map_congr_left
  intro atom _
  simp [childOf]

theorem neighbors_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (atom : Nat) :
    (mol.canonicalIncidentNeighbors (σ atom)).Perm ((mol.canonicalIncidentNeighbors atom).map σ) := by
  rw [List.perm_ext_iff_of_nodup (mol.canonicalIncidentNeighbors_nodup _ unique)
    ((mol.canonicalIncidentNeighbors_nodup _ unique).map sym.injective)]
  intro y
  rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed, List.mem_map]
  constructor
  · intro positive
    obtain ⟨x, rfl⟩ := sym.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed]
    rwa [sym.bonds] at positive
  · rintro ⟨x, member, rfl⟩
    rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed] at member
    rw [sym.bonds]
    exact member

/-- **Children are covariant up to order.** -/
theorem children_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) :
    (mol.canonicalChildren (mapNode σ node)).Perm ((mol.canonicalChildren node).map (mapNode σ)) := by
  cases real : node.forcedLeaf with
  | true =>
      rw [canonicalChildren_forcedLeaf mol node real,
        canonicalChildren_forcedLeaf mol (mapNode σ node) (by rw [mapNode_forcedLeaf]; exact real)]
      exact List.Perm.refl _
  | false =>
      rw [canonicalChildren_eq mol wellFormed single node real,
        canonicalChildren_eq mol wellFormed single (mapNode σ node)
          (by rw [mapNode_forcedLeaf]; exact real), mapNode_atom, mapNode_parent, List.map_map]
      refine (((neighbors_map sym wellFormed unique node.atom).erase _).map _).trans ?_
      rw [← List.map_erase sym.injective, List.map_map]
      apply List.Perm.of_eq
      apply List.map_congr_left
      intro atom _
      simp only [Function.comp_def, childOf_map sym]

theorem mem_children_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node child : Node) (member : child ∈ mol.canonicalChildren node) :
    mapNode σ child ∈ mol.canonicalChildren (mapNode σ node) :=
  (children_map sym wellFormed unique single node).mem_iff.mpr (List.mem_map_of_mem member)

/-! ## Reachability -/

theorem reachedFrom_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (center : Nat) (node : Node) (reached : ReachedFrom mol center node) :
    ReachedFrom mol (σ center) (mapNode σ node) := by
  induction reached with
  | refl => exact .refl
  | tail _ edge ih => exact ih.tail (mem_children_map sym wellFormed unique single _ _ edge)

/-- **Reachability is covariant.** -/
theorem reached_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (reached : Reached mol node) : Reached mol (mapNode σ node) := by
  obtain ⟨center, valid, path⟩ := reached
  exact ⟨σ center, sym.inRange center valid, reachedFrom_map sym wellFormed unique single center
    node path⟩

/-! ## Frames -/

/-- Optional atom lists that agree up to order after relabelling the second. -/
def OptionPermMap (σ : Nat → Nat) : Option (List Nat) → Option (List Nat) → Prop
  | none, none => True
  | some l', some l => l'.Perm (l.map σ)
  | _, _ => False

theorem optionPermMap_none_none (σ : Nat → Nat) : OptionPermMap σ none none = True := rfl
theorem optionPermMap_some_some (σ : Nat → Nat) (l' l : List Nat) :
    OptionPermMap σ (some l') (some l) = l'.Perm (l.map σ) := rfl
theorem optionPermMap_none_some (σ : Nat → Nat) (l : List Nat) :
    OptionPermMap σ none (some l) = False := rfl
theorem optionPermMap_some_none (σ : Nat → Nat) (l' : List Nat) :
    OptionPermMap σ (some l') none = False := rfl

theorem frameAtomsOf_cursors_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (real : node.forcedLeaf = false) :
    (frameAtomsOf (occurrenceLigandCursors mol (mapNode σ node))).Perm
      ((frameAtomsOf (occurrenceLigandCursors mol node)).map σ) := by
  rw [occurrence_atoms mol node real,
    occurrence_atoms mol (mapNode σ node) (by rw [mapNode_forcedLeaf]; exact real),
    canonicalOriginalParent?_map, List.map_append, Option.map_map]
  refine List.Perm.append (List.Perm.of_eq ?_) ?_
  · cases canonicalOriginalParent? node <;> rfl
  · rw [List.map_map]
    refine ((children_map sym wellFormed unique single node).map _).trans (List.Perm.of_eq ?_)
    rw [List.map_map]
    rfl

theorem cursors_length_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (real : node.forcedLeaf = false) :
    (occurrenceLigandCursors mol (mapNode σ node)).length =
      (occurrenceLigandCursors mol node).length := by
  have := (frameAtomsOf_cursors_map sym wellFormed unique single node real).length_eq
  simpa [frameAtomsOf] using this

/-- **Frames are covariant up to order**, including the lone-pair phantom, at in-range
occurrence atoms. -/
theorem frameAtoms_map {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (valid : node.atom < mol.atomCount) :
    OptionPermMap σ (frameAtoms? mol (mapNode σ node)) (frameAtoms? mol node) := by
  cases real : node.forcedLeaf with
  | true =>
      rw [frameAtoms?_forcedLeaf mol node real,
        frameAtoms?_forcedLeaf mol (mapNode σ node) (by rw [mapNode_forcedLeaf]; exact real),
        optionPermMap_none_none]
      exact trivial
  | false =>
      have ligandsLength : (mol.ligandsWithLonePair (σ node.atom)).length =
          (mol.ligandsWithLonePair node.atom).length := by
        rw [(sym.ligands node.atom valid).length_eq, List.length_map]
      have ligandsPhantom : (mol.ligandsWithLonePair (σ node.atom)).contains mol.atomCount =
          (mol.ligandsWithLonePair node.atom).contains mol.atomCount := by
        apply Bool.eq_iff_iff.mpr
        rw [List.contains_iff_mem, List.contains_iff_mem, (sym.ligands node.atom valid).mem_iff]
        conv_lhs => rw [← sym.phantom]
        rw [List.mem_map]
        constructor
        · rintro ⟨x, member, eq⟩
          rw [sym.injective eq] at member
          exact member
        · intro member
          exact ⟨_, member, rfl⟩
      have cursors := frameAtomsOf_cursors_map sym wellFormed unique single node real
      have length := cursors_length_map sym wellFormed unique single node real
      unfold frameAtoms? occurrenceLigandFrame?
      simp only [mapNode_atom, ligandsLength, ligandsPhantom, length]
      by_cases four : (mol.ligandsWithLonePair node.atom).length != 4
      · simp only [four, ↓reduceIte, Option.map_none, optionPermMap_none_none]
      · simp only [four, Bool.false_eq_true, ↓reduceIte]
        by_cases physical : (occurrenceLigandCursors mol node).length == 4
        · simp only [physical, ↓reduceIte, Option.map_some, optionPermMap_some_some]
          exact cursors
        · simp only [physical, Bool.false_eq_true, ↓reduceIte]
          by_cases three : ((occurrenceLigandCursors mol node).length == 3 &&
              (mol.ligandsWithLonePair node.atom).contains mol.atomCount) = true
          · simp only [three, ↓reduceIte, Option.map_some, optionPermMap_some_some]
            unfold frameAtomsOf
            rw [List.map_append, List.map_append, List.map_append]
            refine List.Perm.append cursors (List.Perm.of_eq ?_)
            simp [RawMolecule.canonicalPhantom, sym.phantom]
          · simp only [three, Bool.false_eq_true, ↓reduceIte, Option.map_none,
              optionPermMap_none_none]

theorem frameAtoms_map_some {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (valid : node.atom < mol.atomCount) :
    ∃ atoms', frameAtoms? mol (mapNode σ node) = some atoms' ∧ atoms'.Perm (atoms.map σ) := by
  have := frameAtoms_map sym wellFormed unique single node valid
  rw [frame] at this
  cases h : frameAtoms? mol (mapNode σ node) with
  | none => rw [h, optionPermMap_none_some] at this; exact this.elim
  | some atoms' => rw [h, optionPermMap_some_some] at this; exact ⟨atoms', rfl, this⟩

theorem frameAtoms_map_none {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (frame : frameAtoms? mol node = none) (valid : node.atom < mol.atomCount) :
    frameAtoms? mol (mapNode σ node) = none := by
  have := frameAtoms_map sym wellFormed unique single node valid
  rw [frame] at this
  cases h : frameAtoms? mol (mapNode σ node) with
  | none => rfl
  | some atoms' => rw [h, optionPermMap_some_none] at this; exact this.elim

/-- A frame at the relabelled occurrence comes from a frame at the original occurrence. -/
theorem frameAtoms_map_some' {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    (node : Node) (atoms' : List Nat) (frame : frameAtoms? mol (mapNode σ node) = some atoms')
    (valid : node.atom < mol.atomCount) :
    ∃ atoms, frameAtoms? mol node = some atoms ∧ atoms'.Perm (atoms.map σ) := by
  have := frameAtoms_map sym wellFormed unique single node valid
  rw [frame] at this
  cases h : frameAtoms? mol node with
  | none => rw [h, optionPermMap_some_none] at this; exact this.elim
  | some atoms => rw [h, optionPermMap_some_some] at this; exact ⟨atoms, rfl, this⟩

/-! ## Facts and states -/

/-- The relabelled temporary fact. -/
def mapFact (σ : Nat → Nat) (fact : OccurrenceAuxFact) : OccurrenceAuxFact where
  key := ⟨fact.key.history.map σ, fact.key.provenance⟩
  atom := σ fact.atom
  descriptor := fact.descriptor
  uppercase := fact.uppercase
  priorityPositions := fact.priorityPositions

theorem mapFact_key (σ : Nat → Nat) (fact : OccurrenceAuxFact) :
    (mapFact σ fact).key = ⟨fact.key.history.map σ, fact.key.provenance⟩ := rfl

theorem mapFact_mapFact {mol : RawMolecule} {σ : Nat → Nat} (sym : Symmetry mol σ)
    (fact : OccurrenceAuxFact) : mapFact σ (mapFact σ fact) = fact := by
  cases fact with
  | mk key atom descriptor uppercase positions =>
      cases key
      simp [mapFact, sym.apply_apply, sym.map_map]

theorem factOf_map (σ : Nat → Nat) (node : Node) (d : LocalizedTetrahedralRSPseudoDescriptor) :
    factOf (mapNode σ node) d = mapFact σ (factOf node d) := by
  cases d with
  | chiral raw => rfl
  | pseudoasymmetric pseudo => cases pseudo <;> rfl

theorem mapFact_key_injective {mol : RawMolecule} {σ : Nat → Nat} (sym : StructuralSymmetry mol σ)
    (a b : OccurrenceAuxFact) (eq : (mapFact σ a).key = (mapFact σ b).key) : a.key = b.key := by
  have hist : a.key.history.map σ = b.key.history.map σ := by
    have h := congrArg CanonicalOccurrenceKey.history eq
    exact h
  have prov : a.key.provenance = b.key.provenance := by
    have h := congrArg CanonicalOccurrenceKey.provenance eq
    exact h
  have hist' : a.key.history = b.key.history := sym.injective.list_map hist
  calc a.key = ⟨a.key.history, a.key.provenance⟩ := rfl
    _ = ⟨b.key.history, b.key.provenance⟩ := by rw [hist', prov]
    _ = b.key := rfl

/-! ## Geometry -/

/-- The pulled-back geometry: coordinates of the relabelled atom. -/
def pullback (σ : Nat → Nat) (geom : Geometry) : Geometry := fun atom => geom (σ atom)

/-- **Readback of a relabelled priority list is readback under the pulled-back geometry.** -/
theorem readback_map (σ : Nat → Nat) (geom : Geometry) (l : List Nat) :
    readback? geom (l.map σ) = readback? (pullback σ geom) l := by
  unfold readback?
  rw [List.mapM_map]
  rfl

theorem mirror_pullback (σ : Nat → Nat) (geom : Geometry) :
    mirror (pullback σ geom) = pullback σ (mirror geom) := rfl

theorem pullback_pullback {mol : RawMolecule} {σ : Nat → Nat} (sym : Symmetry mol σ)
    (geom : Geometry) : pullback σ (pullback σ geom) = geom := by
  funext atom
  simp [pullback, sym.apply_apply]

end TetraStereo.OneCenter.LocalizedChemicalRingRelabel

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.mapNode_mapNode
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.canonicalChildren_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.neighbors_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.children_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.reached_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.frameAtoms_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.frameAtoms_map_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.frameAtoms_map_some'
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.factOf_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.readback_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.StructuralSymmetry.inverse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.mapNode_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRelabel.mapFact_key_injective
