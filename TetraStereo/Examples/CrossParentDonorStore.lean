import TetraStereo.Engine.RingBridgeheadPaths
import TetraStereo.Engine.RingAtomicNeighborReport
import TetraStereo.Engine.RingOppositeDonorArms
import TetraStereo.Examples.MixedHalogenSpiro

/-! Public frozen donor readings on the explicit 41-atom Rule4bCrossParent.mol
graph and the two coordinate controls obtained by exchanging F and Cl. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentDonorStore
open OneCenter Engine
open LocalizedChemicalRing (Input)
open RingAtomicNeighborOrder (Decision neighbors)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (frozen Cell)
open RingGroupedReport (origin)
open private bound toAtom raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder

def molecule : RawMolecule := {
  atoms := ([.C,.N,.N,.N,.N,.N,.N,.C,.C,.C,.C,.C,
    .C,.C,.C,.F,.Cl,.H,.F,.Cl,.H,.F,.Cl,.H,
    .F,.Cl,.H,.F,.Cl,.H,.F,.Cl,.H,.F,.Cl,.H,
    .F,.Cl,.H,.O,.S] : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(0,2),(0,39),(39,40),(40,0),(1,3),(1,4),(2,5),
    (2,6),(3,7),(7,15),(7,16),(7,17),(3,8),(8,18),(8,19),
    (8,20),(4,9),(9,21),(9,22),(9,23),(4,10),(10,24),(10,25),
    (10,26),(5,11),(11,27),(11,28),(11,29),(5,12),(12,30),(12,31),
    (12,32),(6,13),(13,33),(13,34),(13,35),(6,14),(14,36),(14,37),
    (14,38)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩ }

private def point (a b c : Int) : CartesianPoint3 := ⟨(a:ℚ)/10,(b:ℚ)/10,(c:ℚ)/10⟩

def original : SpatialConfiguration := ⟨[point 0 0 0,point (-30) 0 10,point 30 0 10,
    point (-50) (-30) 20,point (-50) 30 20,point 50 (-30) 20,
    point 50 30 20,point (-60) (-40) 30,point (-60) (-20) 30,
    point (-60) 20 30,point (-60) 40 30,point 60 (-40) 30,
    point 60 (-20) 30,point 60 20 30,point 60 40 30,
    point (-66) (-46) 24,point (-66) (-34) 36,point (-54) (-46) 36,
    point (-66) (-26) 36,point (-66) (-14) 24,point (-54) (-14) 36,
    point (-66) 26 36,point (-66) 14 24,point (-54) 14 36,
    point (-66) 46 24,point (-66) 34 36,point (-54) 46 36,
    point 66 (-34) 36,point 66 (-46) 24,point 54 (-46) 36,
    point 66 (-26) 36,point 66 (-14) 24,point 54 (-14) 36,
    point 66 26 36,point 66 14 24,point 54 14 36,
    point 66 34 36,point 66 46 24,point 54 46 36,
    point 0 10 (-10),point 0 (-10) (-10)]⟩

private def swapLeaf (x : SpatialConfiguration) (j : Nat) : SpatialConfiguration :=
  let f := 15 + 3*j
  ⟨(x.positions.set f (x.positions.getD (f+1) (point 0 0 0))).set (f+1) (x.positions.getD f (point 0 0 0))⟩

def geometry (variant : Fin 3) := if variant.val = 0 then original else
  if variant.val = 1 then swapLeaf original 2 else swapLeaf (swapLeaf original 2) 4

def hand (variant : Fin 3) (j : Fin 8) : RS :=
  let orig : RS := if j.val ∈ [0,1,4,6] then .R else .S
  if variant.val ≠ 0 ∧ j.val = 2 ∨ variant.val = 2 ∧ j.val = 4 then orig.swap else orig

def ligandRow (j : Fin 8) : List Nat := [16+3*j.val,15+3*j.val,3+j.val/2,17+3*j.val]
def cell (h : RS) : Cell := some (some (.chiral h,.chiral h.swap))

set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

private def incident (n : Nat) := (List.range molecule.atomCount).filter fun k => 0 < molecule.bondOrder n k

private theorem shell : ∀ j : Fin 8,
    (ligandRow j).Perm (incident (7+j.val)) ∧
    ((ligandRow j).map (RingAtomicNeighborOrder.atomicNumber molecule)).Pairwise (· > ·) ∧
    ∀ a ∈ ligandRow j, ∀ b ∈ ligandRow j,
      RingAtomicNeighborOrder.atomicNumber molecule a = RingAtomicNeighborOrder.atomicNumber molecule b → a = b := by
  decide +kernel

private theorem leaf_rank (j : Fin 8) :
    RingAtomicNeighborOrder.classify? molecule (7+j.val) = some (.ranked (ligandRow j)) := by
  let k := RingAtomicNeighborOrder.atomicNumber molecule
  obtain ⟨p,desc,inj⟩ := shell j
  have leg := RingStereoSiblingPass.legal_order k (incident (7+j.val))
  have same : neighbors molecule (7+j.val) = ligandRow j := by
    apply List.Perm.eq_of_pairwise _ (List.pairwise_map.mp leg.descending)
      (List.pairwise_map.mp (desc.imp le_of_lt)) (leg.perm.trans p.symm)
    intro a b ha hb ab ba
    exact inj a ((leg.perm.trans p.symm).mem_iff.mp ha) b hb (le_antisymm ba ab)
  have inside : 7+j.val < molecule.atomCount := by change 7+j.val < 41; omega
  have nd := desc.imp (fun x => ne_of_gt x)
  simp [RingAtomicNeighborOrder.classify?,inside,RingAtomicNeighborOrder.separated,same,ligandRow] at nd ⊢
  tauto

theorem coordinates : ∀ (v : Fin 3) (j : Fin 8),
    some ((Decision.ranked (ligandRow j)).read (geometry v)) = cell (hand v j) := by decide +kernel

/-- At every real occurrence of a donor, the public store publishes its measured hand,
including when the rerooted direction points toward its nitrogen parent. -/
theorem public_leaf {i : Input} (graph : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : Fin 3) (xyz : i.spatial = geometry v)
    (q : Site i) (a : i.certified.Atom) (j : Fin 8) (id : a.val = 7+j.val)
    (real : q.val.node.provenance = .realAtom) (atId : q.val.node.current? = some a) :
    RingChemicalGraphProof.state i q = cell (hand v j) := by
  have pub := RingAtomicNeighborOrder.ranked_state i admit q a real atId (ligandRow j)
    (by rw [graph,id]; exact leaf_rank j)
  rw [xyz] at pub
  exact pub.trans (coordinates v j)

private def atIndex (i : Input) (graph : i.molecule = molecule) (a : Fin 41) : i.certified.Atom :=
  toAtom i a.val (by rw [graph]; exact a.isLt)

private def route (j : Fin 8) : List Nat := [7+j.val,3+j.val/2,1+j.val/4,0]

private theorem bonds : ∀ j : Fin 8,
    0 < molecule.bondOrder 0 (1+j.val/4) ∧
    0 < molecule.bondOrder (1+j.val/4) (3+j.val/2) ∧
    0 < molecule.bondOrder (3+j.val/2) (7+j.val) := by decide +kernel

/-- Each of the eight specified publications is actually present in the frozen
reader of the C1 origin on the corresponding nitrogen branch. -/
theorem observed {i : Input} (graph : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : Fin 3) (xyz : i.spatial = geometry v)
    (j : Fin 8) :
    ∃ q : Site i, q.val.node.history.map Fin.val = route j ∧
      frozen (RingChemicalGraphProof.state i) (origin i (atIndex i graph 0)) q = cell (hand v j) := by
  let root := atIndex i graph 0
  let arm := atIndex i graph ⟨1+j.val/4,by omega⟩
  let par := atIndex i graph ⟨3+j.val/2,by omega⟩
  let leaf := atIndex i graph ⟨7+j.val,by omega⟩
  obtain ⟨b1,b2,b3⟩ := bonds j
  have adj {a b : Fin 41} (edge : 0 < molecule.bondOrder a.val b.val) :
      i.certified.moleculeGraph.Adj (atIndex i graph a) (atIndex i graph b) := by
    apply (raw_adj i _ _).mpr
    rwa [graph]
  have r0 : root.val = 0 := rfl
  have r1 : arm.val = 1+j.val/4 := rfl
  have r2 : par.val = 3+j.val/2 := rfl
  have r3 : leaf.val = 7+j.val := rfl
  have p : RingGraphPaths.Path i root [leaf,par,arm,root] leaf := by
    refine .step (.step (.step .origin
      (adj (a := 0) (b := ⟨1+j.val/4,by omega⟩) b1) ?_)
      (adj (a := ⟨1+j.val/4,by omega⟩) (b := ⟨3+j.val/2,by omega⟩) b2) ?_)
      (adj (a := ⟨3+j.val/2,by omega⟩) (b := ⟨7+j.val,by omega⟩) b3) ?_
    all_goals (simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,r0,r1,r2,r3]; omega)
  let q := RingGraphPaths.site p
  obtain ⟨same,hist,real,cur⟩ := RingGraphPaths.represents_site p
  have len := RingGraphPaths.path_length (RingGraphPaths.represents_site p)
  have dist : RingActiveDistanceSchedule.distance q = 3 := by
    change 4 = RingActiveDistanceSchedule.distance q + 1 at len
    omega
  have ne : leaf ≠ root := by
    intro eq
    have contra : 7+j.val = 0 := congrArg Fin.val eq
    omega
  refine ⟨q,by rw [hist]; rfl,?_⟩
  have value := public_leaf graph admit v xyz q leaf j rfl real cur
  change frozen (RingChemicalGraphProof.state i) (origin i root) q = _
  unfold frozen
  change (if q.val.root ≠ root then _ else if 0 < RingActiveDistanceSchedule.distance q ∧
    q.val.node.current? ≠ some root then _ else _) = _
  have sr : q.val.root = root := same
  rw [if_neg (not_not_intro sr),if_pos ⟨by omega,fun e => ne (Option.some.inj (cur.symm.trans e))⟩]
  exact value

private theorem converted : molecule.toSemanticMolecule?.isSome = true := by decide +kernel
private def semantic : SemanticMolecule := molecule.toSemanticMolecule?.get converted
private theorem semantic_eq : molecule.toSemanticMolecule? = some semantic := (Option.some_get converted).symm

private def source (v : Fin 3) : AuthoritativeChemicalInput :=
  ⟨semantic,some (geometry v),some molecule.toDiagramConfiguration⟩

private theorem readyGraph : semantic.localizedCIPGraphReady? = true := by decide +kernel
private theorem well (v : Fin 3) : (source v).StructurallyWellFormed := by
  exact ⟨(semantic.localizedCIPGraphReady?_eq_true_iff.mp readyGraph).1,
    (by fin_cases v <;> decide +kernel : (geometry v).positions.length = semantic.atomCount),
    by change True ∧ true = true ∧ true = true; decide⟩

private def cert (v : Fin 3) : CertifiedLocalizedCIPInput :=
  ⟨⟨source v,well v⟩,semantic.localizedCIPGraphReady?_eq_true_iff.mp readyGraph⟩

private theorem admissibleMol : molecule.StereochemicalAdmissible :=
  molecule.stereochemicalAdmissible?_eq_true_iff.mp (by decide +kernel)

private theorem supported : ∀ b ∈ molecule.bonds, b.kind.IsLocalizedCovalent := by
  have test : molecule.bonds.all (fun b => decide (b.kind = .single)) = true := by decide +kernel
  intro b hb
  rw [of_decide_eq_true ((List.all_eq_true.mp test) b hb)]
  exact ⟨1,rfl⟩

private theorem rawBond (v : Fin 3) (a b : (cert v).Atom) :
    (cert v).moleculeGraph.bond a b = molecule.bondOrder a.val b.val :=
  moleculeGraph_bond_eq_rawBondOrder _ _
    ⟨semantic_eq,rfl⟩ admissibleMol.1.1 admissibleMol.1.2 supported a b

private theorem order_one : ∀ a b : Fin 41, 0 < molecule.bondOrder a.val b.val →
    molecule.bondOrder a.val b.val = 1 := by decide +kernel

def input (v : Fin 3) : Input :=
  ⟨cert v,molecule,geometry v,⟨semantic_eq,rfl⟩,rfl,admissibleMol,supported,
    by intro a b adjacent; change 0 < (cert v).moleculeGraph.bond a b at adjacent
       rw [rawBond] at adjacent ⊢; exact order_one a b adjacent,
    ⟨0,by change ∀ a : Fin 41, (cert v).moleculeGraph.formalCharge a = 0
          intro a; change (semantic.atoms.get a).formalCharge = 0
          exact (by decide +kernel : ∀ a : Fin 41, (semantic.atoms.get a).formalCharge = 0) a⟩⟩

open private coordinates_of_neighbor_volumes neighbors directVolume from TetraStereo.Examples.MixedHalogenSpiro

private def physicalNeighbors (a : Fin 41) :=
  (List.finRange 41).filter fun b => decide (0 < molecule.bondOrder a.val b.val)

private def volume (v : Fin 3) (xs : List (Fin 41)) : Option ℚ := do
  let a ← (geometry v).positions[(← xs[0]?).val]?
  let b ← (geometry v).positions[(← xs[1]?).val]?
  let c ← (geometry v).positions[(← xs[2]?).val]?
  let d ← (geometry v).positions[(← xs[3]?).val]?
  return CartesianPoint3.orientedVolume a b c d

private theorem nonflat : ∀ (v : Fin 3) (a : Fin 41), (physicalNeighbors a).length = 4 →
    (volume v (physicalNeighbors a)).any (· != 0) = true := by decide +kernel

theorem admitted (v : Fin 3) : LocalizedChemicalRing.coordinatesAdmitted (input v) = true := by
  apply coordinates_of_neighbor_volumes
  intro a
  have ns : neighbors (cert v) a = physicalNeighbors a := by
    apply List.filter_congr
    intro b _
    change decide (0 < (cert v).moleculeGraph.bond a b) = _
    rw [rawBond]
  change (neighbors (cert v) a).length = 4 →
    (directVolume (cert v) (neighbors (cert v) a)).any (· != 0) = true
  rw [ns]
  exact nonflat v a

theorem fixture_observed (v : Fin 3) (j : Fin 8) :
    ∃ (root : (input v).certified.Atom) (q : Site (input v)), root.val = 0 ∧
      q.val.node.history.map Fin.val = route j ∧
      frozen (RingChemicalGraphProof.state (input v)) (origin (input v) root) q = cell (hand v j) := by
  have hit : LocalizedChemicalRing.admitRawSpatial? molecule (geometry v) = some (input v) :=
    RingSpatialTransport.readmit (input v)
  obtain ⟨g,s⟩ := RingChemicalReport.admission_fields hit
  obtain ⟨q,h,w⟩ := observed g (admitted v) v s j
  exact ⟨_,q,rfl,h,w⟩

/-- The raw report returns exactly the eight independently measured donor pairs,
in any requested order and with repetitions allowed. -/
theorem raw_donors (v : Fin 3) (requested : List (Fin 8)) :
    RingHydrogenReport.fromRaw? molecule (geometry v) (requested.map (fun j => 7+j.val)) =
    some (requested.map fun j => (7+j.val,(cell (hand v j)).join)) := by
  have hit : LocalizedChemicalRing.admitRawSpatial? molecule (geometry v) = some (input v) :=
    RingSpatialTransport.readmit (input v)
  obtain ⟨g,xyz⟩ := RingChemicalReport.admission_fields hit
  have closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel
  have cover : RingAtomicNeighborOrder.covered molecule (requested.map (fun j => 7+j.val)) = true := by
    apply List.all_eq_true.mpr
    intro n hn
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hn
    simp [leaf_rank j]
  have eqn := RingAtomicNeighborOrder.closed_report (input v) (admitted v) (g ▸ closed)
    (requested.map (fun j => 7+j.val)) (g ▸ cover)
  rw [g,xyz] at eqn
  rw [eqn]
  clear eqn cover
  unfold RingAtomicNeighborOrder.directReport?
  induction requested with
  | nil => rfl
  | cons j js ih =>
    have measured := congrArg Option.join (coordinates v j)
    simp only [Option.join_some] at measured
    simp only [List.map_cons,List.mapM_cons,leaf_rank,Option.map_some,measured,ih]
    rfl

private theorem types : ∀ a : Fin 41, (incident a.val).length = 4 →
    a.val = 0 ∨ (7 ≤ a.val ∧ a.val < 15) := by decide +kernel

private def branch (j : Fin 6) (a : Fin 41) : Nat :=
  ((#[#[0,1,0,3,4,0,0,3,3,4,4,0,0,0,0,3,3,3,3,3,3,4,4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    #[0,0,2,0,0,5,6,0,0,0,0,5,5,6,6,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,5,5,5,6,6,6,6,6,6,0,0],
    #[1,1,1,3,1,1,1,7,8,1,1,1,1,1,1,7,7,7,8,8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    #[1,1,1,1,4,1,1,1,1,9,10,1,1,1,1,1,1,1,1,1,1,9,9,9,10,10,10,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    #[2,2,2,2,2,5,2,2,2,2,2,11,12,2,2,2,2,2,2,2,2,2,2,2,2,2,2,11,11,11,12,12,12,2,2,2,2,2,2,2,2],
    #[2,2,2,2,2,2,6,2,2,2,2,2,2,13,14,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,13,13,13,14,14,14,2,2]] : Array (Array Nat)).getD j.val #[]).getD a.val 41

private def nit (j : Fin 6) : Fin 41 := ⟨1+j.val,by omega⟩
private def edge (a b : Fin 41) := decide (0 < molecule.bondOrder a.val b.val)

private theorem cuts : ∀ j : Fin 6,
    (∀ u : Fin 41, edge (nit j) u = true → branch j u = u.val) ∧
    (∀ u v : Fin 41, u ≠ nit j → v ≠ nit j → edge u v = true → branch j u = branch j v) := by
  decide +kernel

private theorem same_branch (j : Fin 6) (xs : List (Fin 41)) (b : Fin 41) (hb : b ≠ nit j) :
    ∀ a : Fin 41, a ≠ nit j → (∀ x ∈ xs, x ≠ nit j) →
      RingBridgeheadNitrogen.OrderedBonds edge a xs b → branch j a = branch j b := by
  induction xs with
  | nil => exact fun a na _ ed => (cuts j).2 _ _ na hb ed
  | cons x xs ih =>
    intro a na exclude h
    have nx := exclude x List.mem_cons_self
    exact ((cuts j).2 _ _ na nx h.1).trans (ih x nx (fun z hz => exclude z (List.mem_cons_of_mem _ hz)) h.2)

private theorem unique_first (j : Fin 6) {b : Fin 41} (hb : b ≠ nit j) {xs}
    (p : RingBridgeheadNitrogen.SimpleInterior edge (nit j) b xs) :
    ∃ x ∈ xs, x.val = branch j b := by
  cases xs with
  | nil => exact (p.nonempty rfl).elim
  | cons x xs =>
    have h := p.bonds
    exact ⟨x,List.mem_cons_self,((cuts j).1 x h.1).symm.trans (same_branch j xs b hb x
      (p.endpoints x List.mem_cons_self).1
      (fun v hv => (p.endpoints v (List.mem_cons_of_mem _ hv)).1) h.2)⟩

private theorem bridge (j : Fin 6) : RingBridgeheadNitrogen.constrainedRaw molecule (nit j).val = false := by
  unfold RingBridgeheadNitrogen.constrainedRaw
  rw [dif_pos (show (nit j).val < molecule.atomCount from (nit j).isLt)]
  change RingBridgeheadNitrogen.test edge (nit j) = false
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨w⟩ := RingBridgeheadNitrogen.paths_of_test _ _ yes
  obtain ⟨u,hu,eu⟩ := unique_first j w.distinct.symm w.common_path
  obtain ⟨v,hv,ev⟩ := unique_first j w.distinct.symm w.left_path
  exact w.common_left u hu (Fin.ext (eu.trans ev.symm) ▸ hv)

private theorem no_ring_neighbors : ∀ (j : Fin 6) (v : Fin 41), molecule.bondOrder (nit j).val v.val = 1 →
    RingOxaziridineNitrogen.atomIs molecule v.val .O = false ∧
    RingOxaziridineNitrogen.atomIs molecule v.val .Cl = false := by decide +kernel

private theorem constrained (j : Fin 6) : RingPyramidalNitrogen.constrainedRaw molecule (nit j).val = false := by
  have ox : RingOxaziridineNitrogen.constrainedRaw molecule (nit j).val = false := by
    unfold RingOxaziridineNitrogen.constrainedRaw
    rw [dif_pos (show (nit j).val < molecule.atomCount from (nit j).isLt)]
    apply decide_eq_false
    rintro ⟨_,o,_,iso,ed,_⟩
    exact Bool.noConfusion (iso.symm.trans ((no_ring_neighbors j o ed).1))
  have cl : RingChloroaziridineNitrogen.constrainedRaw molecule (nit j).val = false := by
    unfold RingChloroaziridineNitrogen.constrainedRaw
    rw [dif_pos (show (nit j).val < molecule.atomCount from (nit j).isLt)]
    apply decide_eq_false
    rintro ⟨_,c,isc,ed,_⟩
    exact Bool.noConfusion (isc.symm.trans ((no_ring_neighbors j c ed).2))
  have dia : RingDialkyldiaziridine.constrainedRaw molecule (nit j).val = false := by
    unfold RingDialkyldiaziridine.constrainedRaw
    rw [dif_pos (show (nit j).val < molecule.atomCount from (nit j).isLt)]
    apply decide_eq_false
    rintro ⟨_,m,_,_,nm,c,_,nc,mc,_⟩
    have noTriangle : ∀ (k : Fin 6) (a b : Fin 41), molecule.bondOrder (nit k).val a.val = 1 →
        molecule.bondOrder (nit k).val b.val = 1 → molecule.bondOrder a.val b.val ≠ 1 := by
      decide +kernel
    exact noTriangle j m c nm nc mc
  have alkoxy : RingAlkoxyaziridineNitrogen.constrainedRaw molecule (nit j).val = false := by
    unfold RingAlkoxyaziridineNitrogen.constrainedRaw
    rw [dif_pos (show (nit j).val < molecule.atomCount from (nit j).isLt)]
    apply decide_eq_false
    rintro ⟨_,o,iso,ed,_⟩
    exact Bool.noConfusion (iso.symm.trans ((no_ring_neighbors j o ed).1))
  simp [RingPyramidalNitrogen.constrainedRaw,ox,cl,bridge,dia,alkoxy]

private theorem pyramids (a : Fin 41) : RingAtomicNeighborOrder.neutralPyramidal molecule a.val = false := by
  by_cases h : 1 ≤ a.val ∧ a.val < 7
  · let j : Fin 6 := ⟨a.val-1,by omega⟩
    have eq : nit j = a := Fin.ext (by dsimp [nit,j]; omega)
    rw [←eq]
    have con := constrained j
    unfold RingAtomicNeighborOrder.neutralPyramidal
    rw [con]
    exact (by decide +kernel : ∀ k : Fin 6, (molecule.atoms[(nit k).val]?).any (fun x =>
      ((x.element == .P || x.element == .As || x.element == .Sb) || x.element == .N && false) &&
        x.charge == 0 && !x.aromatic) = false) j
  · have check : ∀ a : Fin 41, ¬(1 ≤ a.val ∧ a.val < 7) →
        (molecule.atoms[a.val]?).any (fun x => x.element == .P || x.element == .As ||
          x.element == .Sb || x.element == .N) = false := by decide +kernel
    have no := check a h
    unfold RingAtomicNeighborOrder.neutralPyramidal
    cases look : molecule.atoms[a.val]? with
    | none => rfl
    | some x =>
      rw [look] at no
      simp only [Option.any_some,Bool.or_eq_false_iff] at no
      simp [no]

/-- Exact signed contents of the public frozen reader. The focus itself is masked.
The other eight eligible atom IDs contribute only at real occurrences. -/
def expectedView {i : Input} (v : Fin 3) (q : Site i) : Cell :=
  let a := RingAllLigandTwoShell.siteAtom i q
  if h : q.val.node.provenance = .realAtom ∧ 7 ≤ a.val ∧ a.val < 15 then
    cell (hand v ⟨a.val-7,by omega⟩)
  else some none

theorem reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : Fin 3) (xyz : i.spatial = geometry v)
    (f : Site i) (root : f.val.root.val = 0) :
    frozen (RingChemicalGraphProof.state i) f = frozen (expectedView v) f := by
  funext q
  unfold frozen
  split_ifs with off vis
  · rfl
  · let a := RingAllLigandTwoShell.siteAtom i q
    have cur := RingAllLigandTwoShell.site_current i q
    dsimp only [expectedView]
    split_ifs with good
    · exact public_leaf graph ok v xyz q a _ (by dsimp [a]; omega) good.1 cur
    · apply (RingChemicalGraphProof.state_eq i q).trans
      apply RingChemicalGraphProof.skips i
      rintro ⟨real,b,hb,eligible⟩
      obtain rfl : b = a := Option.some.inj (hb.symm.trans cur)
      have size : a.val < 41 := by have t := bound i a; rwa [graph] at t
      have ph : RingPyramidalPublication.phosphorus i a = false := by
        change (RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val && _) = false
        rw [graph,pyramids ⟨a.val,size⟩]; rfl
      have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
        simpa [RingPyramidalPublication.eligible,ph] using eligible
      rw [RingAtomicNeighborOrder.degree_eq,graph] at four
      have len := (RingStereoSiblingPass.legal_order (RingAtomicNeighborOrder.atomicNumber molecule)
        (incident a.val)).perm.length_eq
      rcases types ⟨a.val,size⟩ (len.symm.trans four) with zero|leaf
      · exact vis.2 (cur.trans (congrArg some (Fin.ext (zero.trans root.symm))))
      · exact good ⟨real,leaf⟩
  · rfl

/-- Closed list of simple histories from the root, newest endpoint first. -/
private def histories : List (List Nat) :=
  [[0],[1,0],[2,0],[39,0],[40,0],[3,1,0],[4,1,0],[5,2,0],[6,2,0],[40,39,0],[39,40,0]] ++
    (List.finRange 8).flatMap fun j =>
      let h := route j
      [h,(15+3*j.val)::h,(16+3*j.val)::h,(17+3*j.val)::h]

private theorem continues : ∀ h ∈ histories, ∀ n : Fin 41,
    0 < molecule.bondOrder (h.headD 41) n.val → n.val ∉ h → n.val :: h ∈ histories := by decide +kernel

private theorem listed {i : Input} (graph : i.molecule = molecule) {r a h}
    (zero : r.val = 0) (p : RingGraphPaths.Path i r h a) :
    (h.map Fin.val).headD 41 = a.val ∧ h.map Fin.val ∈ histories := by
  induction p with
  | origin => exact ⟨rfl,by simp only [List.map_singleton,zero]; decide +kernel⟩
  | @step hist cur next prev ed fresh ih =>
    have size : next.val < 41 := by have k := bound i next; rwa [graph] at k
    refine ⟨rfl,continues _ ih.2 ⟨next.val,size⟩ ?_ ?_⟩
    · rw [ih.1,←graph]; exact (raw_adj i _ _).mp ed
    · intro mem
      obtain ⟨t,ht,eq⟩ := List.mem_map.mp mem
      exact fresh (Fin.ext eq ▸ ht)

private theorem leaf_history : ∀ j : Fin 8, ∀ h ∈ histories,
    h.headD 41 = 7+j.val → h = route j := by decide +kernel

/-- From C1 each donor has only one real occurrence, so the eight observed
entries are eight occurrences as well as eight distinct atoms. -/
theorem unique_history {i : Input} (graph : i.molecule = molecule) (q : Site i)
    (root : q.val.root.val = 0) (real : q.val.node.provenance = .realAtom)
    (j : Fin 8) (donor : (q.val.node.current?.map Fin.val) = some (7+j.val)) :
    q.val.node.history.map Fin.val = route j := by
  obtain ⟨a,atA,p⟩ := RingGraphPaths.site_path q real
  obtain ⟨lastAtom,entry⟩ := listed graph root p
  rw [atA] at donor
  exact leaf_history j _ entry (lastAtom.trans (Option.some.inj donor))

/-- First the four donors in the N2 arm, then the four in the N3 arm.
The middle control changes one hand, and the last changes a second hand. -/
def expectedHands (v : Fin 3) : List RS :=
  if v.val = 0 then [.R,.R,.S,.S, .R,.S,.R,.S]
  else if v.val = 1 then [.R,.R,.R,.S, .R,.S,.R,.S]
  else [.R,.R,.R,.S, .S,.S,.R,.S]

/-- All eight entries are read from one actual public prior. Every entry carries both
the original and reflected hands. The specified histories locate their parent groups. -/
theorem fixture_table (v : Fin 3) :
    ∃ (root : (input v).certified.Atom) (qs : Fin 8 → Site (input v)), root.val = 0 ∧
      (∀ j, (qs j).val.node.history.map Fin.val = route j) ∧
      (List.finRange 8).map (fun j => frozen (RingChemicalGraphProof.state (input v))
        (origin (input v) root) (qs j)) = (expectedHands v).map cell := by
  choose qs loc seen using fun j => observed (i := input v) rfl (admitted v) v rfl j
  refine ⟨atIndex (input v) rfl 0,qs,rfl,loc,?_⟩
  simp only [seen]
  fin_cases v <;> decide +kernel

end TetraStereo.Examples.CrossParentDonorStore
assert_kernel_only TetraStereo.Examples.CrossParentDonorStore.fixture_observed
assert_kernel_only TetraStereo.Examples.CrossParentDonorStore.raw_donors
assert_kernel_only TetraStereo.Examples.CrossParentDonorStore.reader
assert_kernel_only TetraStereo.Examples.CrossParentDonorStore.unique_history
assert_kernel_only TetraStereo.Examples.CrossParentDonorStore.fixture_table
