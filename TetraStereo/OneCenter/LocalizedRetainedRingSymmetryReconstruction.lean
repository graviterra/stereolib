import TetraStereo.OneCenter.MoleculeGraph
import TetraStereo.OneCenter.Symmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-!
# Forward observations of retained cut arms

`ArmPathForward` is one direction of a path correspondence. It preserves length, `dropLast`,
terminal atomic number, mass, and formal charge, and the bond from every earlier index to the
terminal. It does not supply an inverse, and it is not claimed to be injective or surjective on
paths or on atoms.

`EndpointConsistent` is an extra hypothesis of the derived renaming `atomMap`; it is not an
existence theorem. The separate `LocalizedRetainedCoherentSymmetry` development formalizes full
residual-path observations and finite entry-matching lemmas.
`DeclarativeCIPBoundaryComponentReconstruction` constructs from a full two-sided residual
equivalence a coherent component isomorphism and a root-fixing automorphism. No descent of an
arbitrary path correspondence to an atom map is claimed.

The valence-complete bicyclo[1.1.0]butane carrier below is a raw `MoleculeGraph (Fin 10)`, not a
certified input. `bicycloGen 8` decides twelve concrete lists. That decision is not a proof that
those lists are all `IsArmPath`s, and `bicycloImage` is not an `ArmPathForward`. The two paths
ending at hydrogen `4` are sent to paths ending at `4` and `5`, so this pairing is not a function
on atoms. The same graph still has the bridgehead reflection, so the pairing is not a
counterexample to existence of some root-fixing automorphism.
-/

namespace TetraStereo.OneCenter.RetainedRingSymmetryReconstruction

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Consecutive positive bonds along a root-first path. -/
def BondedChain (m : MoleculeGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | x :: y :: t => 0 < m.bond x y ∧ BondedChain m (y :: t)

/-- A retained cut-arm path: a simple bonded walk of length at least two, rooted at `root`,
whose second atom is the ligand. Ring duplicates are not extra vertices; they are later
references to an earlier index on this same path. -/
structure IsArmPath (m : MoleculeGraph V) (root ligand : V) (p : List V) : Prop where
  two_le : 2 ≤ p.length
  head : p.head? = some root
  second : p[1]? = some ligand
  nodup : p.Nodup
  chain : BondedChain m p

theorem armPath_ne_nil {m : MoleculeGraph V} {root ligand : V} {p : List V}
    (hp : IsArmPath m root ligand p) : p ≠ [] := by
  intro h
  have := hp.two_le
  simp [h] at this

theorem getLast?_arm {m : MoleculeGraph V} {root ligand : V} {p : List V}
    (hp : IsArmPath m root ligand p) :
    p.getLast? = some (p.getLast (armPath_ne_nil hp)) :=
  List.getLast?_eq_some_getLast _

theorem nodup_getLast_ne_head {p : List V} (h : p.Nodup) (hlen : 1 < p.length) :
    p.getLast (by intro hempty; simp [hempty] at hlen) ≠
      p.head (by intro hempty; simp [hempty] at hlen) := by
  intro heq
  cases p with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
          have hmem : x ∈ y :: ys := by
            have hlast : (y :: ys).getLast (by simp) = x := by
              simpa [List.getLast_cons] using heq
            simpa [hlast] using List.getLast_mem (l := y :: ys) (by simp)
          exact (List.nodup_cons.mp h).1 hmem

theorem not_arm_getLast_root {m : MoleculeGraph V} {root ligand : V} {p : List V}
    (hp : IsArmPath m root ligand p) : p.getLast? ≠ some root := by
  intro hlast
  have hlen : 1 < p.length := by
    have htwo := hp.two_le
    omega
  have hne := nodup_getLast_ne_head hp.nodup hlen
  have hhead : p.head (armPath_ne_nil hp) = root := by
    have hheadEq : p.head? = some (p.head (armPath_ne_nil hp)) :=
      List.head?_eq_some_head (armPath_ne_nil hp)
    exact Option.some.inj (hheadEq.symm.trans hp.head)
  have hget : p.getLast (armPath_ne_nil hp) = root := by
    rw [getLast?_arm hp] at hlast
    exact Option.some.inj hlast
  exact hne (hget.trans hhead.symm)

theorem bondedChain_dropLast {m : MoleculeGraph V} {p : List V}
    (h : BondedChain m p) : BondedChain m p.dropLast := by
  induction p with
  | nil => simp [BondedChain, List.dropLast]
  | cons x xs ih =>
      cases xs with
      | nil => simp [BondedChain]
      | cons y ys =>
          cases ys with
          | nil => simp [BondedChain]
          | cons z zs =>
              have hxy : 0 < m.bond x y ∧ BondedChain m (y :: z :: zs) := by
                simpa [BondedChain] using h
              have htail := ih hxy.2
              simpa [List.dropLast, BondedChain] using And.intro hxy.1 htail

theorem take_dropLast_of_le {α : Type*} (p : List α) {k : Nat} (hk : k ≤ p.length - 1) :
    p.dropLast.take k = p.take k := by
  induction p generalizing k with
  | nil =>
      simp at hk
      subst hk
      simp
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hk0 : k = 0 := by simp at hk; omega
          simp [hk0]
      | cons y ys =>
          cases k with
          | zero => simp
          | succ k =>
              simp [List.dropLast, List.take]
              apply ih
              have hlen : (x :: y :: ys).length = (y :: ys).length + 1 := by simp
              have hpos : 0 < (y :: ys).length := by simp
              rw [hlen] at hk
              omega

theorem isArmPath_dropLast {m : MoleculeGraph V} {root ligand : V} {p : List V}
    (hp : IsArmPath m root ligand p) (hlen : 2 < p.length) :
    IsArmPath m root ligand p.dropLast where
  two_le := by
    rw [List.length_dropLast]
    omega
  head := by
    cases p with
    | nil => simp at hlen
    | cons x xs =>
        have hx : x = root := by simpa using hp.head
        cases xs with
        | nil => simp at hlen
        | cons y ys =>
            cases ys with
            | nil => simp at hlen
            | cons z zs => simp [hx, List.dropLast, List.head?]
  second := by
    cases p with
    | nil => simp at hlen
    | cons x xs =>
        cases xs with
        | nil => simp at hlen
        | cons y ys =>
            have hy : some y = some ligand := by simpa using hp.second
            cases hy
            cases ys with
            | nil => simp at hlen
            | cons z zs => simp [List.dropLast]
  nodup := hp.nodup.sublist (List.dropLast_sublist p)
  chain := bondedChain_dropLast hp.chain

/-- One-way path map. Observations are terminal atomic number, mass, and charge, and the bond
order from the terminal back to each earlier index. No inverse is stored. -/
structure ArmPathForward (m : MoleculeGraph V) (root a b : V) where
  φ : List V → List V
  maps : ∀ {p : List V}, IsArmPath m root a p → IsArmPath m root b (φ p)
  length_eq : ∀ {p : List V}, IsArmPath m root a p → (φ p).length = p.length
  dropLast_eq : ∀ {p : List V}, IsArmPath m root a p → 2 < p.length →
    φ p.dropLast = (φ p).dropLast
  base : IsArmPath m root a [root, a]
  ligand_eq : φ [root, a] = [root, b]
  z_eq : ∀ {p : List V} (hp : IsArmPath m root a p),
    m.atomZ ((φ p).getLast (armPath_ne_nil (maps hp))) =
      m.atomZ (p.getLast (armPath_ne_nil hp))
  mass_eq : ∀ {p : List V} (hp : IsArmPath m root a p),
    m.atomMass ((φ p).getLast (armPath_ne_nil (maps hp))) =
      m.atomMass (p.getLast (armPath_ne_nil hp))
  charge_eq : ∀ {p : List V} (hp : IsArmPath m root a p),
    m.formalCharge ((φ p).getLast (armPath_ne_nil (maps hp))) =
      m.formalCharge (p.getLast (armPath_ne_nil hp))
  indexBond_eq : ∀ {p : List V} (hp : IsArmPath m root a p) (i : Nat) (hi : i < p.length),
    m.bond ((φ p).get ⟨i, by simpa [length_eq hp] using hi⟩)
        ((φ p).getLast (armPath_ne_nil (maps hp))) =
      m.bond (p.get ⟨i, hi⟩) (p.getLast (armPath_ne_nil hp))

/-- Paths that already end at the same atom have images ending at the same atom. -/
def EndpointConsistent {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) : Prop :=
  ∀ {p q : List V}, IsArmPath m root a p → IsArmPath m root a q →
    p.getLast? = q.getLast? → (iso.φ p).getLast? = (iso.φ q).getLast?

noncomputable def atomMap {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) (v : V) : V :=
  if h : ∃ p : List V, IsArmPath m root a p ∧ p.getLast? = some v then
    ((iso.φ (Classical.choose h)).getLast? |>.getD v)
  else
    v

theorem atomMap_of_path {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) (hE : EndpointConsistent iso)
    {p : List V} (hp : IsArmPath m root a p) :
    atomMap iso (p.getLast (armPath_ne_nil hp)) =
      (iso.φ p).getLast (armPath_ne_nil (iso.maps hp)) := by
  have hex : ∃ q : List V, IsArmPath m root a q ∧
      q.getLast? = some (p.getLast (armPath_ne_nil hp)) :=
    ⟨p, hp, getLast?_arm hp⟩
  unfold atomMap
  rw [dif_pos hex]
  have hq := Classical.choose_spec hex
  have hsame := hE hq.1 hp (hq.2.trans (getLast?_arm hp).symm)
  have hφ : (iso.φ (Classical.choose hex)).getLast? =
      some ((iso.φ p).getLast (armPath_ne_nil (iso.maps hp))) := by
    rw [hsame, getLast?_arm (iso.maps hp)]
  simp [hφ]

theorem atomMap_root {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) :
    atomMap iso root = root := by
  unfold atomMap
  refine dif_neg ?_
  intro ⟨p, hp, hlast⟩
  exact not_arm_getLast_root hp hlast

theorem atomMap_ligand {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) (hE : EndpointConsistent iso) :
    atomMap iso a = b := by
  have hlast : ([root, a] : List V).getLast (armPath_ne_nil iso.base) = a := by
    simp [List.getLast]
  have himage : (iso.φ [root, a]).getLast (armPath_ne_nil (iso.maps iso.base)) = b := by
    have hsome : (iso.φ [root, a]).getLast? = some b := by
      rw [iso.ligand_eq]
      simp
    rw [getLast?_arm (iso.maps iso.base)] at hsome
    exact Option.some.inj hsome
  have hmap := atomMap_of_path iso hE iso.base
  rw [hlast, himage] at hmap
  exact hmap

theorem isArmPath_take {m : MoleculeGraph V} {root ligand : V} {p : List V}
    (hp : IsArmPath m root ligand p) (k : Nat) (hk : 2 ≤ k) (hle : k ≤ p.length) :
    IsArmPath m root ligand (p.take k) := by
  obtain ⟨n, hn⟩ : ∃ n, p.length = k + n := ⟨p.length - k, by omega⟩
  induction n generalizing p k with
  | zero =>
      have hklen : k = p.length := by omega
      subst hklen
      rw [List.take_length]
      exact hp
  | succ n ih =>
      have hlen : 2 < p.length := by omega
      have hp' := isArmPath_dropLast hp hlen
      have hle' : k ≤ p.dropLast.length := by
        rw [List.length_dropLast]
        omega
      have hn' : p.dropLast.length = k + n := by
        rw [List.length_dropLast]
        omega
      have ihp := ih (p := p.dropLast) (k := k) hp' hk hle' hn'
      rw [take_dropLast_of_le p (by omega)] at ihp
      exact ihp

theorem phi_take {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) {p : List V} (hp : IsArmPath m root a p)
    (k : Nat) (hk : 2 ≤ k) (hle : k ≤ p.length) :
    iso.φ (p.take k) = (iso.φ p).take k := by
  obtain ⟨n, hn⟩ : ∃ n, p.length = k + n := ⟨p.length - k, by omega⟩
  induction n generalizing p k with
  | zero =>
      have hklen : k = p.length := by omega
      have htake : p.take k = p := by simp [hklen, List.take_length]
      have himage : (iso.φ p).take k = iso.φ p := by
        have hlenφ := iso.length_eq hp
        simp [hklen, hlenφ]
      rw [htake, himage]
  | succ n ih =>
      have hlen : 2 < p.length := by omega
      have hp' := isArmPath_dropLast hp hlen
      have hle' : k ≤ p.dropLast.length := by
          rw [List.length_dropLast]; omega
      have hn' : p.dropLast.length = k + n := by
        rw [List.length_dropLast]; omega
      have ihp := ih (p := p.dropLast) (k := k) hp' hk hle' hn'
      rw [take_dropLast_of_le p (by omega)] at ihp
      rw [iso.dropLast_eq hp hlen] at ihp
      have hlenφ := iso.length_eq hp
      rwa [take_dropLast_of_le (iso.φ p) (by rw [hlenφ]; omega)] at ihp

theorem getLast?_take_eq {α : Type*} (p : List α) (i : Nat) (hi : i < p.length) :
    (p.take (i + 1)).getLast? = some (p.get ⟨i, hi⟩) := by
  rw [List.get_eq_getElem, List.getLast?_eq_getElem?]
  have hlen : (p.take (i + 1)).length = i + 1 :=
    List.length_take_of_le (Nat.succ_le_of_lt hi)
  rw [hlen, Nat.add_sub_cancel]
  have hi' : i < (p.take (i + 1)).length := by
    rw [hlen]
    omega
  rw [List.getElem?_eq_getElem hi']
  exact congrArg some List.getElem_take

theorem get_eq_getLast_take {α : Type*} (p : List α) (i : Nat) (hi : i < p.length) :
    p.get ⟨i, hi⟩ =
      (p.take (i + 1)).getLast (by
        intro hempty
        have hlen : (p.take (i + 1)).length = 0 := by simp [hempty]
        rw [List.length_take] at hlen
        omega) := by
  have hne : p.take (i + 1) ≠ [] := by
    intro hempty
    have hlen : (p.take (i + 1)).length = 0 := by simp [hempty]
    rw [List.length_take] at hlen
    omega
  have h := getLast?_take_eq p i hi
  rw [List.getLast?_eq_some_getLast hne] at h
  exact Option.some.inj h.symm

theorem atomMap_get {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) (hE : EndpointConsistent iso)
    {p : List V} (hp : IsArmPath m root a p) (i : Nat) (hi : i < p.length) :
    atomMap iso (p.get ⟨i, hi⟩) =
      (iso.φ p).get ⟨i, by rw [iso.length_eq hp]; exact hi⟩ := by
  cases i with
  | zero =>
      have hroot : p.get ⟨0, hi⟩ = root := by
        have hhead := hp.head
        rw [List.head?_eq_getElem?] at hhead
        rw [List.getElem?_eq_getElem hi] at hhead
        rw [List.get_eq_getElem]
        exact Option.some.inj hhead
      have hφlen : 0 < (iso.φ p).length := by
        rw [iso.length_eq hp]
        exact hi
      have himage : (iso.φ p).get ⟨0, hφlen⟩ = root := by
        have hp' := iso.maps hp
        have hhead := hp'.head
        rw [List.head?_eq_getElem?] at hhead
        rw [List.getElem?_eq_getElem hφlen] at hhead
        rw [List.get_eq_getElem]
        exact Option.some.inj hhead
      rw [hroot, himage]
      exact atomMap_root iso
  | succ j =>
      have hj : j + 1 < p.length := hi
      have hk : 2 ≤ j + 2 := by omega
      have hle : j + 2 ≤ p.length := by omega
      have htake := isArmPath_take hp (j + 2) hk hle
      have hφtake := phi_take iso hp (j + 2) hk hle
      have hmap := atomMap_of_path iso hE htake
      have hlast? : (p.take (j + 2)).getLast? = some (p.get ⟨j + 1, hj⟩) :=
        getLast?_take_eq p (j + 1) hj
      rw [getLast?_arm htake] at hlast?
      have hterm : (p.take (j + 2)).getLast (armPath_ne_nil htake) =
          p.get ⟨j + 1, hj⟩ :=
        Option.some.inj hlast?
      rw [hterm] at hmap
      have hφlen : j + 1 < (iso.φ p).length := by
        rw [iso.length_eq hp]
        exact hj
      have himage? : (iso.φ (p.take (j + 2))).getLast? =
          some ((iso.φ p).get ⟨j + 1, hφlen⟩) := by
        rw [hφtake]
        exact getLast?_take_eq (iso.φ p) (j + 1) hφlen
      rw [getLast?_arm (iso.maps htake)] at himage?
      have himage :
          (iso.φ (p.take (j + 2))).getLast (armPath_ne_nil (iso.maps htake)) =
            (iso.φ p).get ⟨j + 1, hφlen⟩ :=
        Option.some.inj himage?
      rw [himage] at hmap
      exact hmap

/-- A parent step or a return to an earlier index keeps its bond order under the derived renaming. -/
theorem indexBond_atomMap {m : MoleculeGraph V} {root a b : V}
    (iso : ArmPathForward m root a b) (hE : EndpointConsistent iso)
    {p : List V} (hp : IsArmPath m root a p) (i : Nat) (hi : i < p.length) :
    m.bond (atomMap iso (p.get ⟨i, hi⟩))
        (atomMap iso (p.getLast (armPath_ne_nil hp))) =
      m.bond (p.get ⟨i, hi⟩) (p.getLast (armPath_ne_nil hp)) := by
  rw [atomMap_get iso hE hp i hi, atomMap_of_path iso hE hp]
  exact iso.indexBond_eq hp i hi

/-! ## Valence-complete bicyclo[1.1.0]butane -/

/-- `0` root methylene, `1` far methylene, `2` and `3` bridgeheads, `4`/`5` far hydrogens,
`6`/`7` bridgehead hydrogens, `8`/`9` root hydrogens. -/
def bicycloBond (u v : Fin 10) : Nat :=
  let e : List (Fin 10 × Fin 10) :=
    [(0, 2), (2, 0), (0, 3), (3, 0), (0, 8), (8, 0), (0, 9), (9, 0),
      (1, 2), (2, 1), (1, 3), (3, 1), (1, 4), (4, 1), (1, 5), (5, 1),
      (2, 3), (3, 2), (2, 6), (6, 2), (3, 7), (7, 3)]
  if e.contains (u, v) then 1 else 0

def bicyclo : MoleculeGraph (Fin 10) where
  atomZ := fun v => if v.1 ≤ 3 then 6 else 1
  atomMass := fun _ => 0
  formalCharge := fun _ => 0
  bond := bicycloBond
  bond_symm := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide
  bond_self := by
    intro u
    fin_cases u <;> decide

theorem bicyclo_simple : bicyclo.SimpleBonded := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp_all [MoleculeGraph.Adj, bicyclo, bicycloBond]

def bicycloChain : List (Fin 10) → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => decide (0 < bicycloBond x y) && bicycloChain (y :: t)

def bicycloArm (ligand : Fin 10) (p : List (Fin 10)) : Bool :=
  decide (2 ≤ p.length) && (p.head? == some 0) && (p[1]? == some ligand) &&
    decide p.Nodup && bicycloChain p

theorem bondedChain_iff_chain (p : List (Fin 10)) :
    bicycloChain p = true ↔ BondedChain bicyclo p := by
  induction p with
  | nil => simp [bicycloChain, BondedChain]
  | cons x xs ih =>
      cases xs with
      | nil => simp [bicycloChain, BondedChain]
      | cons y ys =>
          simp [bicycloChain, BondedChain, ih, bicyclo]

theorem bicycloArm_iff (ligand : Fin 10) (p : List (Fin 10)) :
    bicycloArm ligand p = true ↔ IsArmPath bicyclo 0 ligand p := by
  constructor
  · intro h
    simp only [bicycloArm] at h
    have hsplit := Bool.and_eq_true_iff.mp h
    have hchain : bicycloChain p = true := hsplit.2
    have hsplit := Bool.and_eq_true_iff.mp hsplit.1
    have hnodup : p.Nodup := decide_eq_true_eq.mp hsplit.2
    have hsplit := Bool.and_eq_true_iff.mp hsplit.1
    have hsecond : p[1]? = some ligand := beq_iff_eq.mp hsplit.2
    have hsplit := Bool.and_eq_true_iff.mp hsplit.1
    have hhead : p.head? = some 0 := beq_iff_eq.mp hsplit.2
    have hlen : 2 ≤ p.length := decide_eq_true_eq.mp hsplit.1
    exact ⟨hlen, hhead, hsecond, hnodup, (bondedChain_iff_chain p).1 hchain⟩
  · intro hp
    have hchain : bicycloChain p = true := (bondedChain_iff_chain p).2 hp.chain
    simp [bicycloArm, hp.two_le, hp.head, hp.second, hp.nodup, hchain]

def bicycloLegal (path : List (Fin 10)) (v : Fin 10) : Bool :=
  match path.getLast?, path.dropLast.getLast? with
  | some last, some parent =>
      decide (0 < bicycloBond last v) && decide (v ∉ path) && decide (v ≠ parent)
  | _, _ => false

def bicycloGen : Nat → List (Fin 10) → List (List (Fin 10))
  | 0, path => [path]
  | fuel + 1, path =>
      path :: ((List.finRange 10).filter (bicycloLegal path)).flatMap
        fun v => bicycloGen fuel (path ++ [v])

/-- Every simple bridgehead path, in expansion order. Twelve paths on each side. -/
theorem bicycloGen_bridgehead_A :
    bicycloGen 8 [0, 2] =
      [[0, 2], [0, 2, 1], [0, 2, 1, 3], [0, 2, 1, 3, 7], [0, 2, 1, 4], [0, 2, 1, 5],
        [0, 2, 3], [0, 2, 3, 1], [0, 2, 3, 1, 4], [0, 2, 3, 1, 5], [0, 2, 3, 7],
        [0, 2, 6]] := by
  decide

theorem bicycloGen_bridgehead_B :
    bicycloGen 8 [0, 3] =
      [[0, 3], [0, 3, 1], [0, 3, 1, 2], [0, 3, 1, 2, 6], [0, 3, 1, 4], [0, 3, 1, 5],
        [0, 3, 2], [0, 3, 2, 1], [0, 3, 2, 1, 4], [0, 3, 2, 1, 5], [0, 3, 2, 6],
        [0, 3, 7]] := by
  decide

def bicycloPairs : List (List (Fin 10) × List (Fin 10)) :=
  [([0, 2], [0, 3]),
    ([0, 2, 1], [0, 3, 1]),
    ([0, 2, 1, 3], [0, 3, 1, 2]),
    ([0, 2, 1, 3, 7], [0, 3, 1, 2, 6]),
    ([0, 2, 1, 4], [0, 3, 1, 4]),
    ([0, 2, 1, 5], [0, 3, 1, 5]),
    ([0, 2, 3], [0, 3, 2]),
    ([0, 2, 3, 1], [0, 3, 2, 1]),
    ([0, 2, 3, 1, 4], [0, 3, 2, 1, 5]),
    ([0, 2, 3, 1, 5], [0, 3, 2, 1, 4]),
    ([0, 2, 3, 7], [0, 3, 2, 6]),
    ([0, 2, 6], [0, 3, 7])]

def bicycloImage (p : List (Fin 10)) : List (Fin 10) :=
  match bicycloPairs.find? fun e => e.1 == p with
  | some e => e.2
  | none => []

def bicycloRingIndices (p : List (Fin 10)) : List Nat :=
  (List.range p.length).filter fun i =>
    match p.getLast?, p.dropLast.getLast?, p[i]? with
    | some last, some parent, some v =>
        decide (0 < bicycloBond last v) && decide (v ≠ parent)
    | _, _, _ => false

def bicycloObs (p : List (Fin 10)) : Option (Nat × Nat × Int × Nat × List Nat) :=
  match p.getLast?, p.dropLast.getLast? with
  | some last, some prev =>
      some (bicyclo.atomZ last, bicyclo.atomMass last, bicyclo.formalCharge last,
        bicycloBond prev last, bicycloRingIndices p)
  | _, _ => none

theorem bicycloPairs_observation :
    (bicycloPairs.all fun e =>
      bicycloImage e.1 == e.2 && bicycloObs e.1 == bicycloObs e.2 &&
        decide (e.1.length = e.2.length) &&
        decide (e.1.length ≤ 2 || bicycloImage e.1.dropLast = e.2.dropLast)) = true := by
  decide

theorem bicycloPairs_are_arms :
    (bicycloPairs.all fun e => bicycloArm 2 e.1 && bicycloArm 3 e.2) = true := by
  decide

theorem bicycloGen_eq_pairs_A :
    bicycloGen 8 [0, 2] = bicycloPairs.map Prod.fst := by
  decide


/-- The two simple paths that both end at far hydrogen `4`. Their images under the observation
bijection end at `4` and `5`. -/
def pathH3aShort : List (Fin 10) := [0, 2, 1, 4]

def pathH3aLong : List (Fin 10) := [0, 2, 3, 1, 4]

theorem pathH3aShort_arm : IsArmPath bicyclo 0 2 pathH3aShort := by
  rw [← bicycloArm_iff]
  decide

theorem pathH3aLong_arm : IsArmPath bicyclo 0 2 pathH3aLong := by
  rw [← bicycloArm_iff]
  decide

theorem pathH3a_same_atom :
    pathH3aShort.getLast (by simp [pathH3aShort]) =
      pathH3aLong.getLast (by simp [pathH3aLong]) := by
  simp [pathH3aShort, pathH3aLong]

theorem bicycloImage_short :
    bicycloImage pathH3aShort = [0, 3, 1, 4] := by
  decide

theorem bicycloImage_long :
    bicycloImage pathH3aLong = [0, 3, 2, 1, 5] := by
  decide

theorem bicycloImage_terminals_ne :
    (bicycloImage pathH3aShort).getLast (by simp [bicycloImage_short]) ≠
      (bicycloImage pathH3aLong).getLast (by simp [bicycloImage_long]) := by
  simp [bicycloImage_short, bicycloImage_long]

/-- No function on the ten atoms pushes both of these terminals. This does not deny that some
other root-fixing automorphism exists. -/
theorem bicyclo_observation_not_atomMap :
    ¬ ∃ f : Fin 10 → Fin 10,
        f (pathH3aShort.getLast (by simp [pathH3aShort])) =
          (bicycloImage pathH3aShort).getLast (by simp [bicycloImage_short]) ∧
        f (pathH3aLong.getLast (by simp [pathH3aLong])) =
          (bicycloImage pathH3aLong).getLast (by simp [bicycloImage_long]) := by
  intro ⟨f, hshort, hlong⟩
  have hsame := pathH3a_same_atom
  have hne := bicycloImage_terminals_ne
  apply hne
  calc
    (bicycloImage pathH3aShort).getLast (by simp [bicycloImage_short])
        = f (pathH3aShort.getLast (by simp [pathH3aShort])) := hshort.symm
    _ = f (pathH3aLong.getLast (by simp [pathH3aLong])) := by rw [hsame]
    _ = (bicycloImage pathH3aLong).getLast (by simp [bicycloImage_long]) := hlong

theorem bicyclo_observation_not_automorphism (e : bicyclo.Aut) :
    ¬ (
      (e : Equiv.Perm (Fin 10)) (pathH3aShort.getLast (by simp [pathH3aShort])) =
        (bicycloImage pathH3aShort).getLast (by simp [bicycloImage_short]) ∧
      (e : Equiv.Perm (Fin 10)) (pathH3aLong.getLast (by simp [pathH3aLong])) =
        (bicycloImage pathH3aLong).getLast (by simp [bicycloImage_long])) := by
  intro h
  exact bicyclo_observation_not_atomMap ⟨(e : Equiv.Perm (Fin 10)), h⟩

end RetainedRingSymmetryReconstruction

assert_kernel_only TetraStereo.OneCenter.RetainedRingSymmetryReconstruction.atomMap_of_path
assert_kernel_only TetraStereo.OneCenter.RetainedRingSymmetryReconstruction.atomMap_root
assert_kernel_only TetraStereo.OneCenter.RetainedRingSymmetryReconstruction.atomMap_ligand
assert_kernel_only TetraStereo.OneCenter.RetainedRingSymmetryReconstruction.indexBond_atomMap
assert_kernel_only TetraStereo.OneCenter.RetainedRingSymmetryReconstruction.bicyclo_observation_not_atomMap
assert_kernel_only TetraStereo.OneCenter.RetainedRingSymmetryReconstruction.bicyclo_observation_not_automorphism
