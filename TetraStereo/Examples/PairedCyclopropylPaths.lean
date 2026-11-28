import TetraStereo.Engine.RingRootTwinDecision

/-! The two cyclopropyl ligands of PairedCyclopropylDonors.mol. Atom
numbers are zero-based and retained histories start at the current atom. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylPaths
open TetraStereo.OneCenter TetraStereo.Engine
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphPaths (Path)
open RingHydrogenSpelling (rawVertices TwinPair)

private def armBonds (a : Nat) : List (Nat × Nat) :=
  [(0,a),(a,a+1),(a,a+2),(a+1,a+2),(a,a+3),(a+1,a+4),(a+2,a+5),(a+2,a+6),
   (a+1,a+7),(a+7,a+8),(a+7,a+9),(a+7,a+10)]

def molecule : RawMolecule where
  atoms := let arm : List Element := [.C,.C,.C,.H,.H,.H,.H,.C,.H,.Cl,.Br]
           (([.C,.F,.H] : List Element) ++ arm ++ arm).map AtomSpec.aliphatic
  bonds := (([(0,1),(0,2)] : List (Nat × Nat)) ++ armBonds 3 ++ armBonds 14).map fun e => ⟨e.1,e.2,.single⟩

private abbrev ID := Fin 25
private def ids (side : Bool) (visit : Fin 5) : List ID :=
  let a : ID := if side then 14 else 3
  let b := a+1
  let c := a+2
  let d := a+7
  ![[a,0],[b,a,0],[d,b,a,0],[b,c,a,0],[d,b,c,a,0]] visit

/-- The direct and detour visits are distinct even where they end at the same atom. -/
def route (side : Bool) (visit : Fin 5) : List Nat := (ids side visit).map Fin.val

/-- Physical ligand carriers in the validation model's descending order. -/
def order (side : Bool) (visit : Fin 5) : List Nat :=
  let a := if side then 14 else 3
  let b := a+1
  let c := a+2
  let d := a+7
  let far := [d+3,d+2,b,d+1]
  ![[0,b,c,a+3],[d,a,c,a+4],far,[d,c,a,a+4],far] visit

def atom (i : Input) (raw : i.molecule = molecule) (n : Fin 25) : i.certified.Atom :=
  (rawVertices i raw).symm n

@[simp] theorem atom_val (i : Input) (raw : i.molecule = molecule) (n : Fin 25) :
    (atom i raw n).val = n.val := rfl

private theorem adj (i : Input) (x y : i.certified.Atom) :
    i.certified.moleculeGraph.Adj x y ↔ 0 < i.molecule.bondOrder x.val y.val :=
  LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported x y

private def legal : List ID → Bool
  | [] => false
  | [a] => a == 0
  | a::b::bs => decide (0 < molecule.bondOrder b.val a.val ∧ a ∉ b::bs) && legal (b::bs)

private theorem routes_legal : ∀ side visit, legal (ids side visit) = true := by decide +kernel

private theorem path_of_legal (i : Input) (raw : i.molecule = molecule) (xs : List ID) (a : ID)
    (ok : legal (a::xs) = true) :
    Path i (atom i raw 0) ((a::xs).map (atom i raw)) (atom i raw a) := by
  induction xs generalizing a with
  | nil =>
    have h : a = 0 := by simpa [legal] using ok
    subst a
    exact .origin
  | cons b bs ih =>
    simp only [legal,Bool.and_eq_true,decide_eq_true_eq] at ok
    apply Path.step (ih b ok.2)
    · exact (adj i _ _).mpr (by simpa [raw] using ok.1.1)
    · intro member
      obtain ⟨c,hc,eq⟩ := List.mem_map.mp member
      exact ok.1.2 (((rawVertices i raw).symm.injective eq) ▸ hc)

/-- Every indicated route has a real retained occurrence on every input with this graph. -/
theorem route_exists (i : Input) (raw : i.molecule = molecule) (side : Bool) (visit : Fin 5) :
    ∃ q : Site i, q.val.root.val = 0 ∧ q.val.node.provenance = .realAtom ∧
      q.val.node.history.map Fin.val = route side visit := by
  have ok := routes_legal side visit
  cases eq : ids side visit with
  | nil => simp [eq,legal] at ok
  | cons a xs =>
    let p := path_of_legal i raw xs a (eq ▸ ok)
    have rep := RingGraphPaths.represents_site p
    refine ⟨RingGraphPaths.site p,congrArg Fin.val rep.1,rep.2.2.1,?_⟩
    rw [rep.2.1,route,eq]
    simp [List.map_map,Function.comp_def]

private def neighbors (n : Nat) := molecule.bonds.filterMap fun e =>
  if e.source == n then some e.target else if e.target == n then some e.source else none

private theorem neighbors_iff : ∀ a b : ID,
    0 < molecule.bondOrder a.val b.val ↔ b.val ∈ neighbors a.val := by decide +kernel

private def donorRoutes := [false,true].flatMap fun s => (List.finRange 5).map (route s)

private def backbone : List (List Nat) :=
  [[0]] ++ donorRoutes ++ [[5,3,0],[5,4,3,0],[16,14,0],[16,15,14,0]]

private def children (h : List Nat) :=
  ((neighbors h.head!).filter (fun n => n ∉ h)).map (· :: h)

private def histories := [[0]] ++ backbone.flatMap children

private theorem closed : histories.all (fun h => (children h).all histories.contains) = true := by
  decide +kernel

private theorem all_histories {i : Input} (raw : i.molecule = molecule) {r : i.certified.Atom}
    (root : r.val = 0) {h a} (p : Path i r h a) : h.map Fin.val ∈ histories := by
  induction p with
  | origin =>
    change [r.val] ∈ histories
    rw [root]
    exact List.mem_append_left _ List.mem_cons_self
  | @step h a b prior bond fresh ih =>
    have head : (h.map Fin.val).head! = a.val := by cases prior <;> rfl
    have existsBond := (adj i a b).mp bond
    rw [raw] at existsBond
    have next := (neighbors_iff (rawVertices i raw a) (rawVertices i raw b)).mp existsBond
    have notMem : b.val ∉ h.map Fin.val := by
      intro mem
      obtain ⟨x,hx,eq⟩ := List.mem_map.mp mem
      exact fresh ((Fin.ext eq) ▸ hx)
    have member : b.val :: h.map Fin.val ∈ children (h.map Fin.val) :=
      List.mem_map.mpr ⟨b.val,List.mem_filter.mpr ⟨head ▸ next,decide_eq_true notMem⟩,rfl⟩
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp closed _ ih) _ member)

private theorem classified : histories.all (fun h =>
    decide (h.head! = 0 ∨ (neighbors h.head!).length ≠ 4 ∨ h ∈ donorRoutes ∨
      h.head! = 5 ∨ h.head! = 16)) = true := by decide +kernel

private theorem count_records : ∀ a : ID,
    ((List.range 25).filter (neighbors a.val).contains).length =
      (neighbors a.val).length ∧ (neighbors a.val).length ≠ 3 := by decide +kernel

private theorem counts (a : ID) :
    (RingAtomicNeighborOrder.neighbors molecule a.val).length = (neighbors a.val).length ∧
      (neighbors a.val).length ≠ 3 := by
  unfold RingAtomicNeighborOrder.neighbors
  rw [(RingStereoSiblingPass.legal_order ..).perm.length_eq]
  have rows : (List.range molecule.atomCount).filter (fun n => decide (0 < molecule.bondOrder a.val n)) =
      (List.range 25).filter (neighbors a.val).contains := by
    apply List.filter_congr
    intro n hn
    have bound : n < 25 := List.mem_range.mp hn
    exact Bool.eq_iff_iff.mpr (by simpa using neighbors_iff a ⟨n,bound⟩)
  rw [rows]
  exact count_records a

private theorem degree (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    Fintype.card (i.certified.moleculeGraph.Neighbor a) = (neighbors a.val).length := by
  rw [RingAtomicNeighborOrder.degree_eq,raw]
  exact (counts (rawVertices i raw a)).1

private theorem no_pyramid (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) :
    RingPyramidalPublication.phosphorus i a = false := by
  have ne : (neighbors a.val).length ≠ 3 := (counts (rawVertices i raw a)).2
  simp [RingPyramidalPublication.phosphorus,degree i raw,ne]

private theorem twins_at (i : Input) (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter)
    (center : c.val.val = 5 ∨ c.val.val = 16) :
    ∃ p : TwinPair i, p.c = c ∧ (atom i raw 0 ≠ p.u) ∧ (atom i raw 0 ≠ p.v) := by
  have pair (parent u v : ID) (atParent : c.val.val = parent.val)
      (good : u ≠ v ∧ (0 : ID) ≠ u ∧ (0 : ID) ≠ v ∧
        (molecule.atoms[u.val]?).map RingRawRenumbering.molecularRecord =
        (molecule.atoms[v.val]?).map RingRawRenumbering.molecularRecord ∧
        (∀ a : ID, molecule.bondOrder u.val a.val = if a = parent then 1 else 0) ∧
        (∀ a : ID, molecule.bondOrder v.val a.val = if a = parent then 1 else 0)) :
      ∃ p : TwinPair i, p.c = c ∧ atom i raw 0 ≠ p.u ∧ atom i raw 0 ≠ p.v := by
    obtain ⟨uv,uz,vz,records,left,right⟩ := good
    have leaf (n : ID) (hn : ∀ j : ID, molecule.bondOrder n.val j.val = if j = parent then 1 else 0)
        (a : i.certified.Atom) : i.molecule.bondOrder (atom i raw n).val a.val =
          if a = c.val then 1 else 0 := by
      rw [raw,atom_val]
      change molecule.bondOrder n.val ((rawVertices i raw) a).val = _
      rw [hn]
      have same : rawVertices i raw a = parent ↔ a = c.val := by
        constructor
        · intro h; exact Fin.ext ((congrArg Fin.val h).trans atParent.symm)
        · rintro rfl; exact Fin.ext atParent
      simp only [same]
    let inj := (rawVertices i raw).symm.injective
    exact ⟨⟨c,atom i raw u,atom i raw v,inj.ne uv,by simpa [raw] using records,leaf u left,leaf v right⟩,
      rfl,inj.ne uz,inj.ne vz⟩
  rcases center with h | h
  · exact pair 5 8 9 h (by decide +kernel)
  · exact pair 16 19 20 h (by decide +kernel)

private theorem path_head {i : Input} {r h a} (p : Path i r h a) :
    (h.map Fin.val).head! = a.val := by cases p <;> rfl

/-- Each donor occurs at an eligible, non-root public auxiliary address. -/
theorem route_candidate (i : Input) (raw : i.molecule = molecule) (side : Bool) (visit : Fin 5) :
    ∃ q : Site i, RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) (atom i raw 0) q ∧
      q.val.node.history.map Fin.val = route side visit := by
  obtain ⟨q,root,real,hist⟩ := route_exists i raw side visit
  obtain ⟨a,current,p⟩ := RingGraphPaths.site_path q real
  have head := path_head p
  rw [hist] at head
  have selected : ∀ s v, (neighbors (route s v).head!).length = 4 ∧ (route s v).head! ≠ 0 := by
    decide +kernel
  obtain ⟨four,other⟩ := selected side visit
  rw [head] at four other
  refine ⟨q,⟨Fin.ext root,?_,real,a,current,?_⟩,hist⟩
  · intro h
    exact other (congrArg Fin.val (Option.some.inj (current.symm.trans h)))
  · simp [RingPyramidalPublication.eligible,degree i raw,four]

/-- Ten distinct retained histories, despite revisiting the same physical donors. -/
theorem route_injective : ∀ s v t w, route s v = route t w → s = t ∧ v = w := by decide +kernel

/-- Every public auxiliary candidate rooted at atom zero is a listed donor
visit or has an explicit pair of identical terminal hydrogen ligands. -/
theorem candidate_cases (i : Input) (raw : i.molecule = molecule) (q : Site i)
    (candidate : RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) (atom i raw 0) q) :
    (∃ side visit, q.val.node.history.map Fin.val = route side visit) ∨
      RingRootTwinDecision.direct i q = some (some none) := by
  obtain ⟨root,other,real,a,current,elig⟩ := candidate
  have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
    simpa [RingPyramidalPublication.eligible,no_pyramid i raw] using elig
  have notRoot : a.val ≠ 0 := fun eq => other (current.trans (congrArg some (Fin.ext eq)))
  obtain ⟨b,hb,p⟩ := RingGraphPaths.site_path q real
  obtain rfl := Option.some.inj (hb.symm.trans current)
  have ok := all_histories raw (congrArg Fin.val root) p
  have head := path_head p
  have classification := of_decide_eq_true (List.all_eq_true.mp classified _ ok)
  rw [head] at classification
  rcases classification with zero | degreeNe | listed | isFive | isSixteen
  · exact (notRoot zero).elim
  · exact (degreeNe ((degree i raw b).symm.trans four)).elim
  · left
    obtain ⟨s,_,hj⟩ := List.mem_flatMap.mp listed
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hj
    exact ⟨s,v,hv.symm⟩
  all_goals
    right
    let c : i.certified.TetrahedralCenter := ⟨b,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    have found : i.certified.localizedOccurrenceDescriptorCenter? q = some c :=
      (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real,hb⟩
    obtain ⟨p,hp,hu,hv⟩ := twins_at i raw c (by first | exact Or.inl isFive | exact Or.inr isSixteen)
    have hit := (RingRootTwinDecision.detected_iff i q.val.root c).mpr
      ⟨p,hp,root ▸ hu,root ▸ hv⟩
    obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp hit
    simp [RingRootTwinDecision.direct,found,hz]

end TetraStereo.Examples.PairedCyclopropylPaths
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPaths.route_exists
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPaths.route_candidate
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPaths.route_injective
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPaths.candidate_cases
