import TetraStereo.Engine.RingChemicalReport

set_option autoImplicit false

/-! Structural correctness of ordinary-hydrogen materialization. The expansion fold
preserves original neighbor rows, appends one bonded leaf per missing hydrogen,
and retains the source atom and coordinate prefixes. -/
namespace TetraStereo.Engine.RingHydrogenCertificate
open OneCenter RingHydrogenCompletion

/-! ## List helpers -/

theorem replicate_add' {α : Type} (m n : ℕ) (a : α) :
    List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  simp

theorem take_append_length {α : Type} (l₁ l₂ : List α) (n : ℕ) (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := by
  exact List.take_left' h

theorem drop_append_length {α : Type} (l₁ l₂ : List α) (n : ℕ) (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := by
  exact List.drop_left' h

theorem drop_append_le {α : Type} (l₁ l₂ : List α) (n : ℕ) (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  exact List.drop_append_of_le_length h

theorem getElem?_none_of_le {α : Type} (l : List α) (t : ℕ) (h : l.length ≤ t) :
    l[t]? = none := by
  exact List.getElem?_eq_none h

theorem getElem?_map_none {α β : Type} (f : α → β) (l : List α) (t : ℕ) (h : l.length ≤ t) :
    (l.map f)[t]? = none :=
  getElem?_none_of_le (l.map f) t (by rw [List.length_map]; exact h)

theorem lt_of_getElem?_eq_some {l : List ℕ} {t q : ℕ} (h : l[t]? = some q) : t < l.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h
  exact bound

theorem drop_set_lt {α : Type} (l : List α) (i n : ℕ) (a : α) (h : i < n) :
    (l.set i a).drop n = l.drop n := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_set_ne (show i ≠ n + j by omega)]

theorem getElem?_set_append_self {α : Type} (rows : List α) (idx : ℕ) (x : α) (extra : List α)
    (h : idx < rows.length) : (rows.set idx x ++ extra)[idx]? = some x := by
  rw [List.getElem?_append_left
    (show idx < (rows.set idx x).length by rw [List.length_set]; exact h)]
  exact List.getElem?_set_self h

theorem getElem?_set_append_ne {α : Type} (rows : List α) (idx i : ℕ) (x : α) (extra : List α)
    (h : i < rows.length) (ne : idx ≠ i) : (rows.set idx x ++ extra)[i]? = rows[i]? := by
  rw [List.getElem?_append_left
    (show i < (rows.set idx x).length by rw [List.length_set]; exact h),
    List.getElem?_set_ne ne]

theorem map_const_eq_map_replicate (idx : ℕ) (l : List ℕ) :
    l.map (fun _ => [idx]) = (List.replicate l.length idx).map (fun q => [q]) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]

theorem getElem?_append_replicate (ps : List ℕ) (k idx t q : ℕ) :
    (ps ++ List.replicate k idx)[t]? = some q ↔
      ps[t]? = some q ∨ (ps.length ≤ t ∧ t - ps.length < k ∧ q = idx) := by
  by_cases lt : t < ps.length
  · rw [List.getElem?_append_left lt]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, _, _⟩)
      · exact h
      · exact absurd lt (Nat.not_lt.mpr h)
  · have le : ps.length ≤ t := Nat.le_of_not_lt lt
    have hnone : ps[t]? = none := getElem?_none_of_le ps t le
    rw [List.getElem?_append_right le, List.getElem?_replicate, hnone]
    by_cases hk : t - ps.length < k
    · rw [if_pos hk]
      constructor
      · intro h
        exact Or.inr ⟨le, hk, (Option.some.inj h).symm⟩
      · rintro (h | ⟨_, _, h⟩)
        · cases h
        · rw [h]
    · rw [if_neg hk]
      constructor
      · intro h
        cases h
      · rintro (h | ⟨_, h, _⟩)
        · cases h
        · exact absurd h hk

theorem flatMap_filterMap_replicate (h : ℕ → ℕ) (l : List ℕ) :
    (l.filterMap (fun i => if h i = 0 then none else some (i, h i))).flatMap
        (fun e => List.replicate e.2 e.1) =
      l.flatMap (fun i => List.replicate (h i) i) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases z : h a = 0
      · have e : (a :: l).filterMap (fun i => if h i = 0 then none else some (i, h i)) =
            l.filterMap (fun i => if h i = 0 then none else some (i, h i)) :=
          List.filterMap_cons_none (by
            show (if h a = 0 then none else some (a, h a)) = none
            exact if_pos z)
        rw [e, ih]
        simp only [List.flatMap_cons, z, List.replicate_zero, List.nil_append]
      · have e : (a :: l).filterMap (fun i => if h i = 0 then none else some (i, h i)) =
            (a, h a) :: l.filterMap (fun i => if h i = 0 then none else some (i, h i)) :=
          List.filterMap_cons_some (by
            show (if h a = 0 then none else some (a, h a)) = some (a, h a)
            exact if_neg z)
        rw [e]
        simp only [List.flatMap_cons, ih]

/-! ## Positive bond order is membership of a connecting record -/

def directedStep (u v : ℕ) (order : ℕ) (bond : RawBond) : ℕ :=
  if bond.directedConnects u v then max order bond.kind.order else order

theorem kind_order_pos (k : ParsedBondKind) : 0 < k.order := by
  cases k <;> decide

theorem directedConnects_iff (b : RawBond) (u v : ℕ) :
    b.directedConnects u v = true ↔ b.source = u ∧ b.target = v := by
  simp [RawBond.directedConnects]

theorem foldl_directed_pos (u v : ℕ) (bonds : List RawBond) (acc : ℕ) :
    0 < bonds.foldl (directedStep u v) acc ↔
      0 < acc ∨ ∃ b, b ∈ bonds ∧ b.source = u ∧ b.target = v := by
  induction bonds generalizing acc with
  | nil =>
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | ⟨b, hb, _⟩)
        · exact h
        · cases hb
  | cons b rest ih =>
      show 0 < rest.foldl (directedStep u v) (directedStep u v acc b) ↔ _
      rw [ih]
      by_cases hc : b.directedConnects u v = true
      · have e : directedStep u v acc b = max acc b.kind.order := if_pos hc
        have hst := (directedConnects_iff b u v).mp hc
        have hpos : 0 < directedStep u v acc b := by
          rw [e]
          exact lt_of_lt_of_le (kind_order_pos b.kind) (le_max_right _ _)
        constructor
        · intro _
          exact Or.inr ⟨b, List.mem_cons.mpr (Or.inl rfl), hst⟩
        · intro _
          exact Or.inl hpos
      · have e : directedStep u v acc b = acc := if_neg hc
        rw [e]
        constructor
        · rintro (h | ⟨b', hb', hc'⟩)
          · exact Or.inl h
          · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', hc'⟩
        · rintro (h | ⟨b', hb', hc'⟩)
          · exact Or.inl h
          · rcases List.mem_cons.mp hb' with eq | hb''
            · rw [eq] at hc'
              exact absurd ((directedConnects_iff b u v).mpr hc') hc
            · exact Or.inr ⟨b', hb'', hc'⟩

theorem directedBondOrder_pos_iff (mol : RawMolecule) (u v : ℕ) :
    0 < mol.directedBondOrder u v ↔ ∃ b, b ∈ mol.bonds ∧ b.source = u ∧ b.target = v := by
  have h := foldl_directed_pos u v mol.bonds 0
  constructor
  · intro pos
    have pos' : 0 < mol.bonds.foldl (directedStep u v) 0 := pos
    rcases h.mp pos' with z | found
    · exact absurd z (Nat.lt_irrefl 0)
    · exact found
  · intro found
    have pos' : 0 < mol.bonds.foldl (directedStep u v) 0 := h.mpr (Or.inr found)
    exact pos'

/-- A pair of atoms has positive bond order exactly when the atoms are distinct and some bond
record joins them, in either orientation. -/
theorem bondOrder_pos_iff (mol : RawMolecule) (u v : ℕ) :
    0 < mol.bondOrder u v ↔
      u ≠ v ∧ ∃ b, b ∈ mol.bonds ∧
        ((b.source = u ∧ b.target = v) ∨ (b.source = v ∧ b.target = u)) := by
  unfold RawMolecule.bondOrder
  by_cases same : u = v
  · rw [if_pos same]
    constructor
    · intro h
      exact absurd h (Nat.lt_irrefl 0)
    · intro h
      exact absurd same h.1
  · have hmax : 0 < max (mol.directedBondOrder u v) (mol.directedBondOrder v u) ↔
        0 < mol.directedBondOrder u v ∨ 0 < mol.directedBondOrder v u := by
      exact lt_max_iff
    rw [if_neg same, hmax, directedBondOrder_pos_iff, directedBondOrder_pos_iff]
    constructor
    · rintro (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
      · exact ⟨same, b, hb, Or.inl h⟩
      · exact ⟨same, b, hb, Or.inr h⟩
    · rintro ⟨_, b, hb, h | h⟩
      · exact Or.inl ⟨b, hb, h⟩
      · exact Or.inr ⟨b, hb, h⟩

/-! ## Splicing never disturbs a filter that rejects the spliced records -/

theorem filter_insertAfterFirst (p q : RawBond → Bool) (extra : List RawBond)
    (hp : extra.filter p = []) (bonds out : List RawBond)
    (observed : RawMolecule.insertAfterFirst q extra bonds = some out) :
    out.filter p = bonds.filter p := by
  induction bonds generalizing out with
  | nil => simp [RawMolecule.insertAfterFirst] at observed
  | cons bond rest ih =>
      simp only [RawMolecule.insertAfterFirst] at observed
      split at observed
      · cases observed
        simp only [List.filter_cons, List.filter_append, hp, List.nil_append]
      · cases mapped : RawMolecule.insertAfterFirst q extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            simp only [List.filter_cons, ih tail mapped]

theorem filter_insertBeforeFirst (p q : RawBond → Bool) (extra : List RawBond)
    (hp : extra.filter p = []) (bonds out : List RawBond)
    (observed : RawMolecule.insertBeforeFirst q extra bonds = some out) :
    out.filter p = bonds.filter p := by
  induction bonds generalizing out with
  | nil => simp [RawMolecule.insertBeforeFirst] at observed
  | cons bond rest ih =>
      simp only [RawMolecule.insertBeforeFirst] at observed
      split at observed
      · cases observed
        simp only [List.filter_cons, List.filter_append, hp, List.nil_append]
      · cases mapped : RawMolecule.insertBeforeFirst q extra rest with
        | none => simp [mapped] at observed
        | some tail =>
            simp [mapped] at observed
            cases observed
            simp only [List.filter_cons, ih tail mapped]

theorem filter_spliceHydrogenBonds (p : RawBond → Bool) (bonds : List RawBond) (idx : ℕ)
    (extra : List RawBond) (hp : extra.filter p = []) :
    (RawMolecule.spliceHydrogenBonds bonds idx extra).filter p = bonds.filter p := by
  unfold RawMolecule.spliceHydrogenBonds
  split
  · rfl
  · cases after : RawMolecule.insertAfterFirst (fun bond => bond.target == idx) extra bonds with
    | some out => exact filter_insertAfterFirst p _ extra hp bonds out after
    | none =>
        cases before :
            RawMolecule.insertBeforeFirst (fun bond => bond.source == idx) extra bonds with
        | some out => exact filter_insertBeforeFirst p _ extra hp bonds out before
        | none =>
            show (bonds ++ extra).filter p = bonds.filter p
            rw [List.filter_append, hp, List.append_nil]

theorem filter_getD (p : RawBond → Bool) (o : Option (List RawBond)) (bonds extra : List RawBond)
    (hp : extra.filter p = [])
    (h : ∀ out, o = some out → out.filter p = bonds.filter p) :
    (o.getD (bonds ++ extra)).filter p = bonds.filter p := by
  cases o with
  | none =>
      show (bonds ++ extra).filter p = bonds.filter p
      rw [List.filter_append, hp, List.append_nil]
  | some out => exact h out rfl

theorem filter_spliceWithPredecessor (p : RawBond → Bool) (pred : Option (Option ℕ))
    (bonds : List RawBond) (idx : ℕ) (extra : List RawBond) (hp : extra.filter p = []) :
    (RawMolecule.spliceHydrogenBondsWithPredecessor pred bonds idx extra).filter p =
      bonds.filter p := by
  unfold RawMolecule.spliceHydrogenBondsWithPredecessor
  split
  · rfl
  · cases pred with
    | none => exact filter_spliceHydrogenBonds p bonds idx extra hp
    | some parent =>
        cases parent with
        | none =>
            show ((RawMolecule.insertBeforeFirst
              (fun bond => bond.source == idx || bond.target == idx) extra bonds).getD
                (bonds ++ extra)).filter p = bonds.filter p
            exact filter_getD p _ bonds extra hp
              (fun out h => filter_insertBeforeFirst p _ extra hp bonds out h)
        | some parent =>
            show ((RawMolecule.insertAfterFirst
              (fun bond => bond.source == parent && bond.target == idx) extra bonds).getD
                (bonds ++ extra)).filter p = bonds.filter p
            exact filter_getD p _ bonds extra hp
              (fun out h => filter_insertAfterFirst p _ extra hp bonds out h)

theorem filter_insertHydrogenInOrder (p : ℕ → Bool) (order : List ℕ) (pre : Bool)
    (hyd : List ℕ) (h : hyd.filter p = []) :
    (RawMolecule.insertHydrogenInOrder order pre hyd).filter p = order.filter p := by
  cases pre with
  | false =>
      show (hyd ++ order).filter p = order.filter p
      rw [List.filter_append, h, List.nil_append]
  | true =>
      cases order with
      | nil =>
          show hyd.filter p = []
          exact h
      | cons first rest =>
          show (first :: (hyd ++ rest)).filter p = (first :: rest).filter p
          simp only [List.filter_cons, List.filter_append, h, List.nil_append]

/-! ## One materialization step, in closed form -/

def freshIds (base count : ℕ) : List ℕ :=
  (List.range count).map fun offset => base + offset

def freshBonds (idx base count : ℕ) : List RawBond :=
  (freshIds base count).map fun target =>
    ({ source := idx, target := target, kind := ParsedBondKind.single } : RawBond)

theorem freshIds_length (base count : ℕ) : (freshIds base count).length = count := by
  unfold freshIds
  rw [List.length_map, List.length_range]

theorem mem_freshBonds (idx base k : ℕ) (b : RawBond) :
    b ∈ freshBonds idx base k ↔
      ∃ off, off < k ∧ b = ⟨idx, base + off, ParsedBondKind.single⟩ := by
  unfold freshBonds freshIds
  constructor
  · intro h
    obtain ⟨target, ht, rfl⟩ := List.mem_map.mp h
    obtain ⟨off, hoff, rfl⟩ := List.mem_map.mp ht
    exact ⟨off, List.mem_range.mp hoff, rfl⟩
  · rintro ⟨off, hoff, rfl⟩
    exact List.mem_map.mpr
      ⟨base + off, List.mem_map.mpr ⟨off, List.mem_range.mpr hoff, rfl⟩, rfl⟩

def stepBody (mol : RawMolecule) (state : RawMolecule.HydrogenExpansionState) (idx : ℕ) :
    RawMolecule.HydrogenExpansionState :=
  (state.1 ++ List.replicate (mol.hydrogenCountAt idx) (AtomSpec.aliphatic Element.H),
    RawMolecule.spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?)
      state.2.1 idx (freshBonds idx state.1.length (mol.hydrogenCountAt idx)),
    (state.2.2.set idx
        (RawMolecule.insertHydrogenInOrder (state.2.2.getD idx [])
          (mol.hydrogenHasPreceding idx)
          (freshIds state.1.length (mol.hydrogenCountAt idx)))) ++
      (freshIds state.1.length (mol.hydrogenCountAt idx)).map (fun _ => [idx]))

theorem step_unfold (mol : RawMolecule) (state : RawMolecule.HydrogenExpansionState) (idx : ℕ) :
    RawMolecule.withExplicitHydrogensStep mol state idx =
      if (mol.hydrogenCountAt idx == 0) = true then state else stepBody mol state idx := rfl

theorem step_zero (mol : RawMolecule) (state : RawMolecule.HydrogenExpansionState) (idx : ℕ)
    (z : mol.hydrogenCountAt idx = 0) :
    RawMolecule.withExplicitHydrogensStep mol state idx = state := by
  have c : (mol.hydrogenCountAt idx == 0) = true := by simp [z]
  rw [step_unfold, if_pos c]

theorem step_pos (mol : RawMolecule) (state : RawMolecule.HydrogenExpansionState) (idx : ℕ)
    (nz : mol.hydrogenCountAt idx ≠ 0) :
    RawMolecule.withExplicitHydrogensStep mol state idx = stepBody mol state idx := by
  have c : ¬ (mol.hydrogenCountAt idx == 0) = true := by simpa using nz
  rw [step_unfold, if_neg c]

theorem candidate?_cases {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (h : candidate? m xyz = some (out, pos)) :
    (plan m = [] ∧ out = m ∧ pos = xyz) ∨
      ∃ extra, addedPositions? m xyz = some extra ∧
        out = (closeHydrogenVertices m).withExplicitHydrogens ∧
        pos = ({ positions := xyz.positions ++ extra } : SpatialConfiguration) := by
  unfold candidate? at h
  by_cases empty : (plan m).isEmpty = true
  · rw [if_pos empty] at h
    have e := Option.some.inj h
    exact Or.inl ⟨List.isEmpty_iff.mp empty, (congrArg Prod.fst e).symm,
      (congrArg Prod.snd e).symm⟩
  · rw [if_neg empty] at h
    obtain ⟨extra, hextra, eqn⟩ := Option.map_eq_some_iff.mp h
    exact Or.inr ⟨extra, hextra, (congrArg Prod.fst eqn).symm, (congrArg Prod.snd eqn).symm⟩

/-- Molecule-level idempotence of construction, for any coordinate row. No hypothesis. -/
theorem candidate?_idempotent {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (h : candidate? m xyz = some (out, pos)) (pos' : SpatialConfiguration) :
    candidate? out pos' = some (out, pos') := by
  have closed := candidate?_closed h
  simp [candidate?, closed]

/-! ## The fold invariant -/

abbrev toRaw (state : RawMolecule.HydrogenExpansionState) : RawMolecule :=
  RawMolecule.HydrogenExpansionState.toRawMolecule state

/-- Complete structural description of an expansion accumulator. `ps` lists the parent of every
hydrogen appended so far, in atom-index order. -/
structure Inv (mol : RawMolecule) (ps : List ℕ)
    (state : RawMolecule.HydrogenExpansionState) : Prop where
  atoms : state.1 = mol.atoms.map RawMolecule.materializedAtomSpec ++
      List.replicate ps.length (AtomSpec.aliphatic Element.H)
  bondsFilter : ∀ p : RawBond → Bool,
      (∀ b : RawBond, mol.atomCount ≤ b.target → p b = false) →
      state.2.1.filter p = mol.bonds.filter p
  bondsMem : ∀ b : RawBond, b ∈ state.2.1 ↔
      b ∈ mol.bonds ∨ ∃ t q, ps[t]? = some q ∧
        b = ⟨q, mol.atomCount + t, ParsedBondKind.single⟩
  rowsLength : state.2.2.length = mol.atomCount + ps.length
  rowsFresh : state.2.2.drop mol.atomCount = ps.map (fun q => [q])
  rowsOriginal : ∀ i, i < mol.atomCount → ∃ row, state.2.2[i]? = some row ∧ row.Nodup ∧
      row.filter (fun j => decide (j < mol.atomCount)) = mol.writtenNeighbors i ∧
      ∀ j, j ∈ row → mol.atomCount ≤ j → ps[j - mol.atomCount]? = some i

theorem Inv.atoms_length {mol : RawMolecule} {ps : List ℕ}
    {state : RawMolecule.HydrogenExpansionState} (inv : Inv mol ps state) :
    state.1.length = mol.atomCount + ps.length := by
  have e := congrArg List.length inv.atoms
  rw [List.length_append, List.length_map, List.length_replicate] at e
  exact e

theorem inv_initial (mol : RawMolecule) (exact : mol.WrittenNeighborExact) :
    Inv mol [] (RawMolecule.initialHydrogenExpansionState mol) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show mol.atoms.map RawMolecule.materializedAtomSpec =
      mol.atoms.map RawMolecule.materializedAtomSpec ++ []
    exact (List.append_nil _).symm
  · intro p _
    rfl
  · intro b
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨t, q, ht, _⟩)
      · exact h
      · simp at ht
  · show ((List.range mol.atomCount).map mol.writtenNeighbors).length = mol.atomCount
    rw [List.length_map, List.length_range]
  · show ((List.range mol.atomCount).map mol.writtenNeighbors).drop mol.atomCount = []
    exact List.drop_eq_nil_iff.mpr (by simp)
  · intro i hi
    have clauses := RawMolecule.WrittenNeighborExact.at mol exact ⟨i, hi⟩
    refine ⟨mol.writtenNeighbors i,
      RawMolecule.getElem?_map_range mol.writtenNeighbors mol.atomCount i hi, clauses.1, ?_, ?_⟩
    · exact List.filter_eq_self.mpr (fun j hj => decide_eq_true (clauses.2.1 j hj))
    · intro j hj hle
      exact absurd (clauses.2.1 j hj) (Nat.not_lt.mpr hle)

/-- Appending `k` hydrogens to the original atom `idx` preserves the invariant, whatever the
splice position of the bonds and whichever insertion slot the written row uses. -/
theorem inv_extend {mol : RawMolecule} {ps : List ℕ}
    {state : RawMolecule.HydrogenExpansionState} (inv : Inv mol ps state)
    (idx k : ℕ) (pred : Option (Option ℕ)) (pre : Bool) (hidx : idx < mol.atomCount) :
    Inv mol (ps ++ List.replicate k idx)
      (state.1 ++ List.replicate k (AtomSpec.aliphatic Element.H),
        RawMolecule.spliceHydrogenBondsWithPredecessor pred state.2.1 idx
          (freshBonds idx state.1.length k),
        (state.2.2.set idx
            (RawMolecule.insertHydrogenInOrder (state.2.2.getD idx []) pre
              (freshIds state.1.length k))) ++
          (freshIds state.1.length k).map (fun _ => [idx])) := by
  have hbase : state.1.length = mol.atomCount + ps.length := inv.atoms_length
  have hrows : state.2.2.length = mol.atomCount + ps.length := inv.rowsLength
  have idxlt : idx < state.2.2.length := by omega
  have idsBounds : ∀ a, a ∈ freshIds state.1.length k →
      state.1.length ≤ a ∧ a < state.1.length + k :=
    fun a ha => RawMolecule.freshHydrogenId_bounds state.1.length k a ha
  have idsFilter :
      (freshIds state.1.length k).filter (fun j => decide (j < mol.atomCount)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha hdec
    have h1 : a < mol.atomCount := of_decide_eq_true hdec
    have h2 := (idsBounds a ha).1
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show state.1 ++ List.replicate k (AtomSpec.aliphatic Element.H) =
      mol.atoms.map RawMolecule.materializedAtomSpec ++
        List.replicate (ps ++ List.replicate k idx).length (AtomSpec.aliphatic Element.H)
    rw [inv.atoms, List.length_append, List.length_replicate, replicate_add',
      List.append_assoc]
  · intro p hpfalse
    have fresh : (freshBonds idx state.1.length k).filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro b hb
      obtain ⟨off, _, rfl⟩ := (mem_freshBonds idx state.1.length k b).mp hb
      have e : p ⟨idx, state.1.length + off, ParsedBondKind.single⟩ = false :=
        hpfalse _ (by
          show mol.atomCount ≤ state.1.length + off
          omega)
      rw [e]
      exact Bool.false_ne_true
    exact (filter_spliceWithPredecessor p pred state.2.1 idx _ fresh).trans
      (inv.bondsFilter p hpfalse)
  · intro b
    show b ∈ RawMolecule.spliceHydrogenBondsWithPredecessor pred state.2.1 idx
      (freshBonds idx state.1.length k) ↔ _
    rw [(RawMolecule.spliceHydrogenBondsWithPredecessor_perm pred state.2.1 idx
        (freshBonds idx state.1.length k)).mem_iff,
      List.mem_append, inv.bondsMem b, mem_freshBonds]
    constructor
    · rintro ((h | ⟨t, q, ht, hb⟩) | ⟨off, hoff, hb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, q, (getElem?_append_replicate ps k idx t q).mpr (Or.inl ht), hb⟩
      · refine Or.inr ⟨ps.length + off, idx,
          (getElem?_append_replicate ps k idx (ps.length + off) idx).mpr
            (Or.inr ⟨Nat.le_add_right _ _, by omega, rfl⟩), ?_⟩
        have e : state.1.length + off = mol.atomCount + (ps.length + off) := by omega
        rw [hb, e]
    · rintro (h | ⟨t, q, ht, hb⟩)
      · exact Or.inl (Or.inl h)
      · rcases (getElem?_append_replicate ps k idx t q).mp ht with h | ⟨le, lt, hq⟩
        · exact Or.inl (Or.inr ⟨t, q, h, hb⟩)
        · refine Or.inr ⟨t - ps.length, lt, ?_⟩
          have e : mol.atomCount + t = state.1.length + (t - ps.length) := by omega
          rw [hb, hq, e]
  · show ((state.2.2.set idx _) ++ (freshIds state.1.length k).map (fun _ => [idx])).length =
      mol.atomCount + (ps ++ List.replicate k idx).length
    simp only [List.length_append, List.length_set, List.length_map, freshIds_length,
      List.length_replicate, hrows]
    omega
  · have hle : mol.atomCount ≤ (state.2.2.set idx
        (RawMolecule.insertHydrogenInOrder (state.2.2.getD idx []) pre
          (freshIds state.1.length k))).length := by
      rw [List.length_set]
      omega
    show ((state.2.2.set idx
        (RawMolecule.insertHydrogenInOrder (state.2.2.getD idx []) pre
          (freshIds state.1.length k))) ++
        (freshIds state.1.length k).map (fun _ => [idx])).drop mol.atomCount =
      (ps ++ List.replicate k idx).map (fun q => [q])
    rw [drop_append_le _ _ _ hle, drop_set_lt _ _ _ _ hidx, inv.rowsFresh, List.map_append,
      map_const_eq_map_replicate idx (freshIds state.1.length k), freshIds_length]
  · intro i hi
    by_cases same : idx = i
    · rw [← same]
      obtain ⟨rowX, hrowX, nodupX, filtX, freshX⟩ := inv.rowsOriginal idx hidx
      have hgetD : state.2.2.getD idx [] = rowX := by
        rw [List.getD_eq_getElem?_getD, hrowX]
        rfl
      rw [hgetD]
      have perm := RawMolecule.insertHydrogenInOrder_perm rowX pre (freshIds state.1.length k)
      have rowBound : ∀ b, b ∈ rowX → b < state.1.length := by
        intro b hb
        by_cases hlt : b < mol.atomCount
        · omega
        · have look := freshX b hb (Nat.le_of_not_lt hlt)
          have bound := lt_of_getElem?_eq_some look
          omega
      refine ⟨RawMolecule.insertHydrogenInOrder rowX pre (freshIds state.1.length k),
        getElem?_set_append_self state.2.2 idx _ _ idxlt, ?_, ?_, ?_⟩
      · refine perm.nodup_iff.mpr ?_
        rw [List.nodup_append]
        refine ⟨RawMolecule.freshHydrogenIds_nodup state.1.length k, nodupX, ?_⟩
        intro a ha b hb eq
        have la := (idsBounds a ha).1
        have lb := rowBound b hb
        omega
      · exact (filter_insertHydrogenInOrder _ rowX pre _ idsFilter).trans filtX
      · intro j hj hle
        rcases List.mem_append.mp (perm.mem_iff.mp hj) with hid | hold
        · have bj := idsBounds j hid
          exact (getElem?_append_replicate ps k idx (j - mol.atomCount) idx).mpr
            (Or.inr ⟨by omega, by omega, rfl⟩)
        · exact (getElem?_append_replicate ps k idx (j - mol.atomCount) idx).mpr
            (Or.inl (freshX j hold hle))
    · obtain ⟨row, hrow, nodup, filt, fresh⟩ := inv.rowsOriginal i hi
      have ilt : i < state.2.2.length := by omega
      refine ⟨row, (getElem?_set_append_ne state.2.2 idx i _ _ ilt same).trans hrow,
        nodup, filt, ?_⟩
      intro j hj hle
      exact (getElem?_append_replicate ps k idx (j - mol.atomCount) i).mpr
        (Or.inl (fresh j hj hle))

theorem inv_step {mol : RawMolecule} {ps : List ℕ}
    {state : RawMolecule.HydrogenExpansionState} (inv : Inv mol ps state)
    (idx : ℕ) (hidx : idx < mol.atomCount) :
    Inv mol (ps ++ List.replicate (mol.hydrogenCountAt idx) idx)
      (RawMolecule.withExplicitHydrogensStep mol state idx) := by
  by_cases z : mol.hydrogenCountAt idx = 0
  · have e : ps ++ List.replicate (mol.hydrogenCountAt idx) idx = ps := by simp [z]
    rw [step_zero mol state idx z, e]
    exact inv
  · rw [step_pos mol state idx z]
    exact inv_extend inv idx (mol.hydrogenCountAt idx) (mol.introductionPredecessors[idx]?)
      (mol.hydrogenHasPreceding idx) hidx

/-- The invariant survives any schedule of original indices, repeated or not. -/
theorem inv_fold (mol : RawMolecule) (idxs : List ℕ)
    (hidx : ∀ i, i ∈ idxs → i < mol.atomCount) :
    ∀ (ps : List ℕ) (state : RawMolecule.HydrogenExpansionState), Inv mol ps state →
      Inv mol (ps ++ idxs.flatMap (fun i => List.replicate (mol.hydrogenCountAt i) i))
        (idxs.foldl (RawMolecule.withExplicitHydrogensStep mol) state) := by
  induction idxs with
  | nil =>
      intro ps state inv
      show Inv mol (ps ++ []) state
      rw [List.append_nil]
      exact inv
  | cons i rest ih =>
      intro ps state inv
      have next := ih (fun j hj => hidx j (List.mem_cons_of_mem _ hj))
        (ps ++ List.replicate (mol.hydrogenCountAt i) i)
        (RawMolecule.withExplicitHydrogensStep mol state i)
        (inv_step inv i (hidx i (List.mem_cons.mpr (Or.inl rfl))))
      rw [List.append_assoc] at next
      rw [List.flatMap_cons, List.foldl_cons]
      exact next

def expandedState (mol : RawMolecule) : RawMolecule.HydrogenExpansionState :=
  (List.range mol.atomCount).foldl (RawMolecule.withExplicitHydrogensStep mol)
    (RawMolecule.initialHydrogenExpansionState mol)

/-- Parent of every materialized hydrogen, in the order of the new atom indices. -/
def parents (mol : RawMolecule) : List ℕ :=
  (List.range mol.atomCount).flatMap (fun i => List.replicate (mol.hydrogenCountAt i) i)

theorem expanded_inv (mol : RawMolecule) (exact : mol.WrittenNeighborExact) :
    Inv mol (parents mol) (expandedState mol) :=
  inv_fold mol (List.range mol.atomCount) (fun _ hi => List.mem_range.mp hi) []
    (RawMolecule.initialHydrogenExpansionState mol) (inv_initial mol exact)

theorem parents_bounded (mol : RawMolecule) :
    ∀ (t q : Nat), (parents mol)[t]? = some q → q < mol.atomCount := by
  intro t q h
  have mem : q ∈ parents mol := List.mem_of_getElem? h
  unfold parents at mem
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.mp mem
  have e : q = i := (List.mem_replicate.mp hq).2
  rw [e]
  exact List.mem_range.mp hi

/-! ## Reading the canonicalized written rows -/

theorem writtenNeighbors_of_row (R : RawMolecule) (c : ℕ) (row : List ℕ)
    (h : R.neighborOrder[c]? = some row) : R.writtenNeighbors c = row := by
  unfold RawMolecule.writtenNeighbors
  rw [h]

theorem exactWrittenNeighbors_filter (R : RawMolecule) (c N : ℕ) (row target : List ℕ)
    (hw : R.writtenNeighbors c = row) (nodup : row.Nodup)
    (valid : ∀ j, j ∈ row → j < R.atomCount ∧ 0 < R.bondOrder c j)
    (filt : row.filter (fun j => decide (j < N)) = target)
    (complete : ∀ j, j < N → 0 < R.bondOrder c j → j ∈ row) :
    (R.exactWrittenNeighbors c).filter (fun j => decide (j < N)) = target := by
  unfold RawMolecule.exactWrittenNeighbors
  rw [hw]
  have preferredFilter :
      row.filter (fun ligand => decide (ligand < R.atomCount ∧ 0 < R.bondOrder c ligand)) =
        row :=
    List.filter_eq_self.mpr (fun j hj => decide_eq_true (valid j hj))
  rw [preferredFilter, List.dedup_eq_self.mpr nodup]
  have missingNil :
      ((((List.range R.atomCount).filter (fun ligand =>
        decide (0 < R.bondOrder c ligand))).filter (fun ligand =>
          decide (ligand ∉ row))).filter (fun j => decide (j < N))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj hlt
    have h1 := List.mem_filter.mp hj
    have h2 := List.mem_filter.mp h1.1
    have notin : j ∉ row := of_decide_eq_true h1.2
    have jlt : j < N := of_decide_eq_true hlt
    have pos : 0 < R.bondOrder c j := of_decide_eq_true h2.2
    exact notin (complete j jlt pos)
  simp only [List.filter_append, filt, missingNil, List.append_nil]

theorem exactWrittenNeighbors_singleton (R : RawMolecule) (c p : ℕ)
    (hw : R.writtenNeighbors c = [p])
    (valid : p < R.atomCount ∧ 0 < R.bondOrder c p)
    (only : ∀ j, j < R.atomCount → 0 < R.bondOrder c j → j = p) :
    R.exactWrittenNeighbors c = [p] := by
  unfold RawMolecule.exactWrittenNeighbors
  rw [hw]
  have preferredFilter :
      ([p] : List ℕ).filter
          (fun ligand => decide (ligand < R.atomCount ∧ 0 < R.bondOrder c ligand)) = [p] :=
    List.filter_eq_self.mpr (fun j hj => by
      have e : j = p := List.mem_singleton.mp hj
      rw [e]
      exact decide_eq_true valid)
  have dd : ([p] : List ℕ).dedup = [p] := List.dedup_eq_self.mpr (List.nodup_singleton p)
  rw [preferredFilter, dd]
  have missingNil :
      ((List.range R.atomCount).filter (fun ligand =>
        decide (0 < R.bondOrder c ligand))).filter (fun ligand => decide (ligand ∉ [p])) =
          [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj hnot
    have h2 := List.mem_filter.mp hj
    have notin : j ∉ [p] := of_decide_eq_true hnot
    have pos : 0 < R.bondOrder c j := of_decide_eq_true h2.2
    exact notin (List.mem_singleton.mpr (only j (List.mem_range.mp h2.1) pos))
  simp only [missingNil, List.append_nil]

/-- The canonical row of an original atom, restricted to original atoms, is its source row. -/
theorem state_row_original {mol : RawMolecule} {ps : List ℕ}
    {state : RawMolecule.HydrogenExpansionState} (inv : Inv mol ps state)
    (exact : mol.WrittenNeighborExact) (i : ℕ) (hi : i < mol.atomCount) :
    ((toRaw state).exactWrittenNeighbors i).filter (fun j => decide (j < mol.atomCount)) =
      mol.writtenNeighbors i := by
  have hbase : state.1.length = mol.atomCount + ps.length := inv.atoms_length
  obtain ⟨row, hrow, nodup, filt, fresh⟩ := inv.rowsOriginal i hi
  have hw : (toRaw state).writtenNeighbors i = row :=
    writtenNeighbors_of_row (toRaw state) i row hrow
  have clauses := RawMolecule.WrittenNeighborExact.at mol exact ⟨i, hi⟩
  refine exactWrittenNeighbors_filter (toRaw state) i mol.atomCount row
    (mol.writtenNeighbors i) hw nodup ?_ filt ?_
  · intro j hj
    by_cases hlt : j < mol.atomCount
    · have mem : j ∈ mol.writtenNeighbors i := by
        rw [← filt]
        exact List.mem_filter.mpr ⟨hj, decide_eq_true hlt⟩
      have pos : 0 < mol.bondOrder i j := (clauses.2.2 ⟨j, hlt⟩).mp mem
      obtain ⟨ne, b, hb, conn⟩ := (bondOrder_pos_iff mol i j).mp pos
      refine ⟨?_, (bondOrder_pos_iff (toRaw state) i j).mpr
        ⟨ne, b, (inv.bondsMem b).mpr (Or.inl hb), conn⟩⟩
      show j < state.1.length
      omega
    · have hle : mol.atomCount ≤ j := Nat.le_of_not_lt hlt
      have look := fresh j hj hle
      have bound := lt_of_getElem?_eq_some look
      have ne : i ≠ j := by omega
      have target : mol.atomCount + (j - mol.atomCount) = j := by omega
      refine ⟨?_, (bondOrder_pos_iff (toRaw state) i j).mpr
        ⟨ne, ⟨i, mol.atomCount + (j - mol.atomCount), ParsedBondKind.single⟩,
          (inv.bondsMem _).mpr (Or.inr ⟨j - mol.atomCount, i, look, rfl⟩),
          Or.inl ⟨rfl, target⟩⟩⟩
      show j < state.1.length
      omega
  · intro j hlt pos
    obtain ⟨ne, b, hb, conn⟩ := (bondOrder_pos_iff (toRaw state) i j).mp pos
    rcases (inv.bondsMem b).mp hb with hold | ⟨t, q, _, hbq⟩
    · have mem : j ∈ mol.writtenNeighbors i :=
        (clauses.2.2 ⟨j, hlt⟩).mpr ((bondOrder_pos_iff mol i j).mpr ⟨ne, b, hold, conn⟩)
      rw [← filt] at mem
      exact (List.mem_filter.mp mem).1
    · rw [hbq] at conn
      rcases conn with ⟨_, h2⟩ | ⟨_, h2⟩
      · have h2' : mol.atomCount + t = j := h2
        omega
      · have h2' : mol.atomCount + t = i := h2
        omega

/-- The canonical row of an appended hydrogen is exactly its parent. -/
theorem state_row_fresh {mol : RawMolecule} {ps : List ℕ}
    {state : RawMolecule.HydrogenExpansionState} (inv : Inv mol ps state)
    (wf : mol.WellFormed) (bounded : ∀ (t q : Nat), ps[t]? = some q → q < mol.atomCount)
    (t q : ℕ) (ht : ps[t]? = some q) :
    (toRaw state).exactWrittenNeighbors (mol.atomCount + t) = [q] := by
  have hq := bounded t q ht
  have hbase : state.1.length = mol.atomCount + ps.length := inv.atoms_length
  have tlt := lt_of_getElem?_eq_some ht
  have e1 : (state.2.2.drop mol.atomCount)[t]? = state.2.2[mol.atomCount + t]? := by
    rw [List.getElem?_drop]
  have hrow : state.2.2[mol.atomCount + t]? = some [q] := by
    rw [← e1, inv.rowsFresh, List.getElem?_map, ht, Option.map_some]
  have hw : (toRaw state).writtenNeighbors (mol.atomCount + t) = [q] :=
    writtenNeighbors_of_row (toRaw state) (mol.atomCount + t) [q] hrow
  have ne : mol.atomCount + t ≠ q := by omega
  refine exactWrittenNeighbors_singleton (toRaw state) (mol.atomCount + t) q hw ⟨?_, ?_⟩ ?_
  · show q < state.1.length
    omega
  · exact (bondOrder_pos_iff (toRaw state) (mol.atomCount + t) q).mpr
      ⟨ne, ⟨q, mol.atomCount + t, ParsedBondKind.single⟩,
        (inv.bondsMem _).mpr (Or.inr ⟨t, q, ht, rfl⟩), Or.inr ⟨rfl, rfl⟩⟩
  · intro j _ pos
    obtain ⟨_, b, hb, conn⟩ := (bondOrder_pos_iff (toRaw state) (mol.atomCount + t) j).mp pos
    rcases (inv.bondsMem b).mp hb with hold | ⟨t', q', ht', hbq⟩
    · have ends := wf b hold
      have hs : b.source < mol.atomCount := ends.1
      have htg : b.target < mol.atomCount := ends.2.1
      rcases conn with ⟨h1, _⟩ | ⟨_, h2⟩
      · omega
      · omega
    · rw [hbq] at conn
      rcases conn with ⟨h1, _⟩ | ⟨h1, h2⟩
      · have h1' : q' = mol.atomCount + t := h1
        have hq' := bounded t' q' ht'
        omega
      · have h1' : q' = j := h1
        have h2' : mol.atomCount + t' = mol.atomCount + t := h2
        have tt : t' = t := by omega
        rw [tt, ht] at ht'
        have qq : q = q' := Option.some.inj ht'
        omega

theorem expanded_writtenNeighbors (mol : RawMolecule) (c : ℕ)
    (hc : c < (expandedState mol).1.length) :
    mol.withExplicitHydrogens.writtenNeighbors c =
      (toRaw (expandedState mol)).exactWrittenNeighbors c :=
  writtenNeighbors_of_row mol.withExplicitHydrogens c _
    (RawMolecule.getElem?_map_range (toRaw (expandedState mol)).exactWrittenNeighbors
      (toRaw (expandedState mol)).atomCount c hc)

/-! ## Transfer through `closeHydrogenVertices` -/

theorem closed_atomCount (m : RawMolecule) :
    (closeHydrogenVertices m).atomCount = m.atomCount := by
  show (m.atoms.map closeAtom).length = m.atoms.length
  rw [List.length_map]

theorem closed_admissible (m : RawMolecule) (adm : m.StereochemicalAdmissible) :
    (closeHydrogenVertices m).StereochemicalAdmissible := by
  have hN := closed_atomCount m
  refine ⟨⟨?_, adm.1.2⟩, ?_⟩
  · intro b hb
    have e : b.source < m.atomCount ∧ b.target < m.atomCount ∧ b.source ≠ b.target :=
      adm.1.1 b hb
    show b.source < (closeHydrogenVertices m).atomCount ∧
      b.target < (closeHydrogenVertices m).atomCount ∧ b.source ≠ b.target
    rw [hN]
    exact e
  · apply RawMolecule.WrittenNeighborExact.of_at
    intro center
    have lt : center.val < m.atomCount := lt_of_lt_of_eq center.isLt hN
    have clauses := RawMolecule.WrittenNeighborExact.at m adm.2 ⟨center.val, lt⟩
    refine ⟨clauses.1, ?_, ?_⟩
    · intro ligand member
      exact lt_of_lt_of_eq (clauses.2.1 ligand member) hN.symm
    · intro ligand
      have llt : ligand.val < m.atomCount := lt_of_lt_of_eq ligand.isLt hN
      exact clauses.2.2 ⟨ligand.val, llt⟩

theorem addedParents_eq (m : RawMolecule) :
    addedParents m = parents (closeHydrogenVertices m) := by
  show ((List.range m.atomCount).filterMap
      (fun i => if missing m i = 0 then none else some (i, missing m i))).flatMap
        (fun e => List.replicate e.2 e.1) =
    (List.range (closeHydrogenVertices m).atomCount).flatMap
      (fun i => List.replicate (missing m i) i)
  rw [closed_atomCount]
  exact flatMap_filterMap_replicate (missing m) (List.range m.atomCount)

theorem heavyCore_materialized_close (a : AtomSpec) :
    heavyCore (RawMolecule.materializedAtomSpec (closeAtom a)) = heavyCore a := by
  unfold closeAtom
  split <;> rfl

theorem map_heavyCore (l : List AtomSpec) :
    ((l.map closeAtom).map RawMolecule.materializedAtomSpec).map heavyCore =
      l.map heavyCore := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih, heavyCore_materialized_close]

/-! ## The certificate -/

/-- Certificate of the materialized molecule with any coordinate tail of the right length. -/
theorem expanded_certified (m : RawMolecule) (xyz : SpatialConfiguration)
    (adm : m.StereochemicalAdmissible) (full : xyz.positions.length = m.atomCount)
    (extra : List Point) (hextra : extra.length = (addedParents m).length) :
    Certified m xyz (closeHydrogenVertices m).withExplicitHydrogens
      ({ positions := xyz.positions ++ extra } : SpatialConfiguration) := by
  have hMN : (closeHydrogenVertices m).atomCount = m.atomCount := closed_atomCount m
  have admM := closed_admissible m adm
  have hps : parents (closeHydrogenVertices m) = addedParents m := (addedParents_eq m).symm
  have inv := expanded_inv (closeHydrogenVertices m) admM.2
  rw [hps] at inv
  have bounded := parents_bounded (closeHydrogenVertices m)
  rw [hps] at bounded
  have hlen : (expandedState (closeHydrogenVertices m)).1.length =
      (closeHydrogenVertices m).atomCount + (addedParents m).length := inv.atoms_length
  have hatoms : (closeHydrogenVertices m).withExplicitHydrogens.atoms =
      (closeHydrogenVertices m).atoms.map RawMolecule.materializedAtomSpec ++
        List.replicate (addedParents m).length (AtomSpec.aliphatic Element.H) := inv.atoms
  have hcount : (closeHydrogenVertices m).withExplicitHydrogens.atomCount =
      m.atomCount + (addedParents m).length := hlen.trans (by rw [hMN])
  have hprefix : ((closeHydrogenVertices m).atoms.map RawMolecule.materializedAtomSpec).length =
      m.atomCount := by
    rw [List.length_map]
    exact hMN
  unfold Certified
  refine ⟨(RawMolecule.stereochemicalAdmissible?_eq_true_iff m).mpr adm, full,
    (RawMolecule.stereochemicalAdmissible?_eq_true_iff _).mpr
      ((closeHydrogenVertices m).withExplicitHydrogens_preserves_stereochemicalAdmissible admM),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [hcount]
    exact Nat.le_add_right _ _
  · show (xyz.positions ++ extra).length =
      (closeHydrogenVertices m).withExplicitHydrogens.atomCount
    rw [List.length_append, full, hextra, hcount]
  · exact take_append_length _ _ _ full
  · rw [hatoms, take_append_length _ _ _ hprefix]
    exact map_heavyCore m.atoms
  · rw [hcount, Nat.add_sub_cancel_left, hatoms]
    exact drop_append_length _ _ _ hprefix
  · have hf := inv.bondsFilter (originalBond m) (fun b hb => by
      show decide (b.source < m.atomCount ∧ b.target < m.atomCount) = false
      apply decide_eq_false
      intro h
      have h2 := h.2
      omega)
    have originals : m.bonds.filter (originalBond m) = m.bonds :=
      List.filter_eq_self.mpr (fun b hb =>
        decide_eq_true ⟨(adm.1.1 b hb).1, (adm.1.1 b hb).2.1⟩)
    exact hf.trans originals
  · apply List.all_eq_true.mpr
    intro b hb
    have hb' := List.mem_filter.mp hb
    have hin : b ∈ (expandedState (closeHydrogenVertices m)).2.1 := hb'.1
    rcases (inv.bondsMem b).mp hin with hold | ⟨t, q, ht, hbq⟩
    · have hob : originalBond m b = true :=
        decide_eq_true ⟨(adm.1.1 b hold).1, (adm.1.1 b hold).2.1⟩
      have hnot : (!originalBond m b) = true := hb'.2
      rw [hob] at hnot
      exact absurd hnot (by decide)
    · have hq := bounded t q ht
      rw [hbq]
      unfold addedBond
      exact decide_eq_true ⟨rfl,
        (show q < m.atomCount by omega),
        (show m.atomCount ≤ (closeHydrogenVertices m).atomCount + t by omega)⟩
  · apply List.all_eq_true.mpr
    intro i hi
    have hi' : i < m.atomCount := List.mem_range.mp hi
    have hiM : i < (closeHydrogenVertices m).atomCount := by omega
    have hc : i < (expandedState (closeHydrogenVertices m)).1.length := by omega
    have row := state_row_original inv admM.2 i hiM
    rw [hMN] at row
    have goal : ((closeHydrogenVertices m).withExplicitHydrogens.writtenNeighbors i).filter
        (fun j => decide (j < m.atomCount)) = m.writtenNeighbors i := by
      rw [expanded_writtenNeighbors _ i hc]
      exact row
    exact decide_eq_true goal
  · rw [hcount, Nat.add_sub_cancel_left]
    apply List.ext_getElem?
    intro t
    by_cases ht : t < (addedParents m).length
    · obtain ⟨q, hq⟩ : ∃ q, (addedParents m)[t]? = some q :=
        ⟨_, List.getElem?_eq_getElem ht⟩
      have hc : m.atomCount + t < (expandedState (closeHydrogenVertices m)).1.length := by
        omega
      have row := state_row_fresh inv admM.1.1 bounded t q hq
      rw [hMN] at row
      have right : ((addedParents m).map (fun p => [p]))[t]? = some [q] := by
        rw [List.getElem?_map, hq, Option.map_some]
      rw [RawMolecule.getElem?_map_range _ _ _ ht, right]
      exact congrArg some ((expanded_writtenNeighbors _ _ hc).trans row)
    · have hle : (addedParents m).length ≤ t := Nat.le_of_not_lt ht
      rw [getElem?_map_none _ (List.range (addedParents m).length) t
          (by rw [List.length_range]; exact hle),
        getElem?_map_none _ (addedParents m) t hle]
  · apply List.all_eq_true.mpr
    intro p hp
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hp
    have hlt := bounded t p ht
    exact decide_eq_true (show p < m.atomCount by omega)

/-- **The gate never refuses a constructed candidate** on an admissible graph with a full
coordinate row. -/
theorem candidate?_certified {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (adm : m.StereochemicalAdmissible) (full : xyz.positions.length = m.atomCount)
    (h : candidate? m xyz = some (out, pos)) : Certified m xyz out pos := by
  rcases candidate?_cases h with ⟨closed, e1, e2⟩ | ⟨extra, hextra, e1, e2⟩
  · rw [e1, e2]
    exact RingChemicalReport.closed_certificate m xyz adm full closed
  · obtain ⟨extra', h', len⟩ := addedPositions?_exists m xyz full
    have same : extra = extra' := Option.some.inj (hextra.symm.trans h')
    have len' : extra.length = (addedParents m).length := by
      rw [same]
      exact len
    rw [e1, e2]
    exact expanded_certified m xyz adm full extra len'

/-- For a constructed candidate the whole executable certificate collapses to its two input
clauses. -/
theorem candidate?_certified_iff {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (h : candidate? m xyz = some (out, pos)) :
    Certified m xyz out pos ↔
      m.StereochemicalAdmissible ∧ xyz.positions.length = m.atomCount :=
  ⟨fun cert => ⟨cert.input_admissible, cert.input_positions⟩,
    fun ok => candidate?_certified ok.1 ok.2 h⟩

/-- On admissible graphs with full coordinates the certified completion is the construction. -/
theorem prepare?_eq_candidate? (m : RawMolecule) (xyz : SpatialConfiguration)
    (adm : m.StereochemicalAdmissible) (full : xyz.positions.length = m.atomCount) :
    prepare? m xyz = candidate? m xyz := by
  show (candidate? m xyz).bind (gate m xyz) = candidate? m xyz
  cases c : candidate? m xyz with
  | none => rfl
  | some r =>
      obtain ⟨out, pos⟩ := r
      have cert := candidate?_certified adm full c
      show gate m xyz (out, pos) = some (out, pos)
      unfold gate
      exact if_pos cert

/-- Totality of the public completion, with its certificate and closure. -/
theorem prepare?_total (m : RawMolecule) (xyz : SpatialConfiguration)
    (adm : m.StereochemicalAdmissible) (full : xyz.positions.length = m.atomCount) :
    ∃ out pos, prepare? m xyz = some (out, pos) ∧ Certified m xyz out pos ∧ plan out = [] := by
  obtain ⟨out, pos, c, _⟩ := candidate?_exists m xyz full
  exact ⟨out, pos, (prepare?_eq_candidate? m xyz adm full).trans c,
    candidate?_certified adm full c, candidate?_closed c⟩

/-- Molecule-level idempotence of the public completion. No hypothesis beyond success. -/
theorem prepare?_idempotent {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (h : prepare? m xyz = some (out, pos)) : prepare? out pos = some (out, pos) := by
  have cert : Certified m xyz out pos := prepare?_certified h
  have closed := prepare?_closed h
  exact prepare?_of_complete out pos closed
    (RingChemicalReport.closed_certificate out pos cert.output_admissible cert.positions_length closed)

end TetraStereo.Engine.RingHydrogenCertificate
assert_kernel_only TetraStereo.Engine.RingHydrogenCertificate.candidate?_certified_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenCertificate.prepare?_eq_candidate?
assert_kernel_only TetraStereo.Engine.RingHydrogenCertificate.prepare?_total
assert_kernel_only TetraStereo.Engine.RingHydrogenCertificate.prepare?_idempotent
