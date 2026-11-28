import TetraStereo.Examples.CrossParentDonorStore
import TetraStereo.Examples.DecalinEarlierTie

/-! Physical donor hands and the unsigned priority classes of the two
nitrogen branches in the 41-atom cross-parent example. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
namespace TetraStereo.Examples.CrossParentClasses
open Engine OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (frozen Cell)
open RingGroupedReport (origin)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open DecalinAuxiliary (history)
open CrossParentDonorStore (molecule ligandRow cell)
open private shell leaf_rank incident types pyramids from TetraStereo.Examples.CrossParentDonorStore
open private bound raw_adj toAtom from TetraStereo.Engine.RingAtomicNeighborOrder
open private canonical_perm from TetraStereo.Examples.DecalinFrames
open private site_eq start from TetraStereo.Examples.DecalinEarlierTie
open private calibrated from TetraStereo.Engine.RingRetainedAuxiliary
open private normalized_frozen erase from TetraStereo.Examples.DecalinEarlierTie
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

def measured (x : SpatialConfiguration) (j : Fin 8) := readback? (RingWrittenPHReadings.geometry x) (ligandRow j)

theorem nonflat {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (j : Fin 8) :
    (measured i.spatial j).isSome = true := by
  let v := toAtom i (7+j.val) (by rw [graph]; change 7+j.val < 41; omega)
  have rows : (RingAtomicNeighborOrder.neighbors molecule (7+j.val)).Perm (ligandRow j) :=
    (RingStereoSiblingPass.legal_order _ _).perm.trans (shell j).1.symm
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph]
    exact rows.length_eq.trans rfl
  let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have all := canonical_perm i c
  rw [graph] at all
  unfold measured
  rw [← RingWrittenPHReadings.inputGeometry_eq]
  exact calibrated i ok c _ (all.trans rows).symm

def hand (x : SpatialConfiguration) (j : Fin 8) := (measured x j).getD .R

theorem public_leaf {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (a : i.certified.Atom) (j : Fin 8) (id : a.val = 7+j.val)
    (real : q.val.node.provenance = .realAtom) (atId : q.val.node.current? = some a) :
    RingChemicalGraphProof.state i q = cell (hand i.spatial j) := by
  have pub := RingAtomicNeighborOrder.ranked_state i ok q a real atId (ligandRow j)
    (by rw [graph,id]; exact leaf_rank j)
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (nonflat graph ok j)
  rw [pub]
  change some ((measured i.spatial j).map _) = _
  simp [hand,hv,cell]

def expectedView {i : Input} (q : Site i) : Cell :=
  let a := RingAllLigandTwoShell.siteAtom i q
  if h : q.val.node.provenance = .realAtom ∧ 7 ≤ a.val ∧ a.val < 15 then
    cell (hand i.spatial ⟨a.val-7,by omega⟩)
  else some none

theorem reader {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (root : f.val.root.val = 0) :
    frozen (RingChemicalGraphProof.state i) f = frozen (expectedView) f := by
  funext q
  unfold frozen
  split_ifs with off vis
  · rfl
  · let a := RingAllLigandTwoShell.siteAtom i q
    have cur := RingAllLigandTwoShell.site_current i q
    dsimp only [expectedView]
    split_ifs with good
    · exact public_leaf graph ok q a _ (by dsimp [a]; omega) good.1 cur
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

/-- XOR permutes the three binary choices on the route to a donor, keeping
each attached F, Cl and H in its corresponding position. -/
def rename (choice : Fin 8) (a : Nat) : Nat :=
  if a = 0 then 0 else if a < 3 then 1 + (a-1 ^^^ choice.val/4)
  else if a < 7 then 3 + (a-3 ^^^ choice.val/2)
  else if a < 15 then 7 + (a-7 ^^^ choice.val)
  else if a < 39 then 15 + 3*((a-15)/3 ^^^ choice.val) + (a-15)%3
  else a

private theorem eq_size (i : Input) (raw : i.molecule = molecule) : RingSpatialTransport.size i = 41 := by
  rw [RingSpatialTransport.size,i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,raw]; rfl

private def parent (a : Nat) := if a < 3 then 0 else if a < 7 then 1+(a-3)/2
  else if a < 15 then 3+(a-7)/2 else if a < 39 then 7+(a-15)/3 else 0

private def bonded (a b : Nat) := (a != 0 && parent a == b) || (b != 0 && parent b == a) ||
  (a == 39 && b == 40) || (a == 40 && b == 39)

private theorem topology : ∀ a b : Fin 41, molecule.bondOrder a.val b.val = (bonded a.val b.val).toNat := by
  decide +kernel

private theorem graph (choice : Fin 8) : ∀ a : Fin 41, rename choice a.val < 41 ∧ rename choice (rename choice a.val) = a.val ∧
    molecule.atoms[rename choice a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : Fin 41, molecule.bondOrder (rename choice a.val) (rename choice b.val) = molecule.bondOrder a.val b.val := by
  have sh : ∀ (c : Fin 8) (a : Fin 41), rename c a.val < 41 ∧ rename c (rename c a.val) = a.val ∧
      molecule.atoms[rename c a.val]? = molecule.atoms[a.val]? := by decide +kernel
  have preserve : ∀ (c : Fin 8) (a b : Fin 41), bonded (rename c a.val) (rename c b.val) = bonded a.val b.val := by decide +kernel
  intro a
  obtain ⟨bound,inv,rec⟩ := sh choice a
  refine ⟨bound,inv,rec,fun b => ?_⟩
  exact (topology ⟨_,bound⟩ ⟨_,(sh choice b).1⟩).trans ((congrArg Bool.toNat (preserve choice a b)).trans (topology a b).symm)

private def index (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) : Fin 41 :=
  ⟨a.val,by rw [←eq_size i raw]; exact a.isLt⟩

private def perm (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) : Equiv.Perm i.certified.Atom :=
  let f (a : i.certified.Atom) : i.certified.Atom := ⟨rename choice a.val,by
    change rename choice a.val < RingSpatialTransport.size i
    rw [eq_size i raw]
    exact (graph choice (index i raw a)).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (graph choice (index i raw a)).2.1
  ⟨f,f,inv,inv⟩

private theorem data : ∀ choice : Fin 8, ∀ a : Fin 41,
    molecule.atomZAt (rename choice a.val) = molecule.atomZAt a.val ∧
    molecule.atomMassAt (rename choice a.val) = molecule.atomMassAt a.val := by decide +kernel

private def aut (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) : i.certified.moleculeGraph.Aut := by
  let e := perm choice i raw
  have phys := LocalizedMarkedCertifiedTerminalRefusal.raw_atom_data i.molecule i.certified i.agreement
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a
    rw [(phys _).1,(phys a).1,raw]
    exact (data choice (index i raw a)).1
  · intro a
    rw [(phys _).2,(phys a).2,raw]
    exact (data choice (index i raw a)).2
  · obtain ⟨k,hk⟩ := i.charge
    exact fun a => (hk _).trans (hk a).symm
  · intro a b
    have em : i.certified.moleculeGraph.Adj (e a) (e b) ↔ i.certified.moleculeGraph.Adj a b := by
      rw [raw_adj,raw_adj,raw]
      change 0 < molecule.bondOrder (rename choice a.val) (rename choice b.val) ↔ _
      exact iff_of_eq (congrArg (fun z => 0 < z) ((graph choice (index i raw a)).2.2.2 (index i raw b)))
    by_cases h : i.certified.moleculeGraph.Adj a b
    · rw [i.single _ _ (em.mpr h),i.single _ _ h]
    · have h' := mt em.mp h
      exact (Nat.eq_zero_of_not_pos h').trans (Nat.eq_zero_of_not_pos h).symm

private theorem records (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) :
    RingGeometryAutomorphism.Records (aut choice i raw) := by
  intro a
  change i.molecule.atoms[rename choice a.val]? = _
  rw [raw]
  exact (graph choice (index i raw a)).2.2.1

noncomputable def carrierFor (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) :=
  RingGeometryAutomorphism.carrier (aut choice i raw) (records choice i raw)


private def image (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (q : Site i) : Site i :=
  RingGeometryAutomorphism.site (aut choice i raw) q

private theorem image_history (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (q : Site i) :
    history (image choice raw q) = (history q).map (rename choice) := by
  simp only [history,image,RingGeometryAutomorphism.site,transportOccurrence_node,mapOfficialNode,List.map_map]
  rfl

private theorem fixed (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) : (aut choice i raw).val root = root := by
  apply Fin.ext
  change rename choice root.val = root.val
  rw [zero]
  rfl

private theorem origin_fixed (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) : image choice raw (origin i root) = origin i root := by
  apply site_eq (fixed choice raw root zero)
  rw [image_history]
  change [rename choice root.val] = [root.val]
  rw [zero]
  rfl

private theorem tip_preserved : ∀ (c : Fin 8) (a : Fin 41),
    (7 ≤ rename c a.val ∧ rename c a.val < 15) ↔ 7 ≤ a.val ∧ a.val < 15 := by decide +kernel

theorem unsignedFor (c : Fin 8) {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0) :
    let r := RingSplitLigandTie.markingReader (frozen (RingChemicalGraphProof.state i) (origin i root))
    RingGeometryExchange.Frozen (carrierFor c i raw) r r := by
  dsimp only
  rw [reader raw ok (origin i root) zero]
  intro q _
  rw [normalized_frozen,normalized_frozen]
  have norm (v : Site i) : erase (expectedView v) = erase (expectedView (image c raw v)) := by
    let a := RingAllLigandTwoShell.siteAtom i v
    have focus := RingAllLigandTwoShell.site_current i v
    have img : RingAllLigandTwoShell.siteAtom i (image c raw v) = (aut c i raw).val a := by
      unfold RingAllLigandTwoShell.siteAtom
      change ((v.val.node.current?.map (aut c i raw).val).getD _) = _
      rw [focus]
      rfl
    have same : (image c raw v).val.node.provenance = v.val.node.provenance := rfl
    have ids : (7 ≤ ((aut c i raw).val a).val ∧ ((aut c i raw).val a).val < 15) ↔
        7 ≤ a.val ∧ a.val < 15 := tip_preserved c (index i raw a)
    unfold expectedView
    simp only [same,img]
    change erase (if _ : v.val.node.provenance = .realAtom ∧ 7 ≤ a.val ∧ a.val < 15 then _ else _) = _
    split_ifs <;> first | rfl | tauto
  have h := RingGeometryAutomorphism.frozen_transport (aut c i raw) (origin i root) q.occurrence
    (s := fun t => erase (expectedView t)) (t := fun t => erase (expectedView t)) (fun v _ => norm v)
  change _ = frozen _ (image c raw (origin i root)) (image c raw q.occurrence) at h
  rwa [origin_fixed c raw root zero] at h

def route (j : Fin 8) : List Nat := [7+j.val,3+j.val/2,1+j.val/4,0]

/-- Three positions after the central carbon: the first N, its child N, and the donor carbon. -/
def prefixHistory (j : Fin 8) (level : Fin 3) := (route j).drop (2-level.val)

def AtLevel {i : Input} (root : i.certified.Atom) (q : Arm i) (j : Fin 8) (n : Fin 3) : Prop :=
  q.occurrence.val.root = root ∧ history q.occurrence = prefixHistory j n ∧
    ∃ p, q.previous? = some p ∧ p.val.root = root ∧ history p = (prefixHistory j n).tail

private def choice (j k : Fin 8) : Fin 8 := ⟨(j.val ^^^ k.val)%8,Nat.mod_lt _ (by decide)⟩

private theorem prefixes : ∀ (j k : Fin 8) (n : Fin 3),
    (prefixHistory j n).map (rename (choice j k)) = prefixHistory k n ∧
    ((prefixHistory j n).tail.map (rename (choice j k))) = (prefixHistory k n).tail := by decide +kernel

private theorem moved {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) (u v : Arm i) (j k : Fin 8) (n : Fin 3)
    (l : AtLevel root u j n) (r : AtLevel root v k n) :
    (carrierFor (choice j k) i raw).image u = v := by
  obtain ⟨lu,lh,p,lp,pr,ph⟩ := l
  obtain ⟨rv,rh,t,rt,tr,th⟩ := r
  let c := choice j k
  have mapSite (x y : Site i) (xr : x.val.root = root) (yr : y.val.root = root)
      (path : (history x).map (rename c) = history y) : image c raw x = y := by
    apply site_eq _ ((image_history c raw x).trans path)
    exact (congrArg (aut c i raw).val xr).trans ((fixed c raw root zero).trans yr.symm)
  have one := mapSite _ _ lu rv (lh ▸ rh ▸ (prefixes j k n).1)
  have two := mapSite _ _ pr tr (ph ▸ th ▸ (prefixes j k n).2)
  cases u with | mk uq up =>
    cases v with | mk vq vp =>
      change up = some p at lp
      change vp = some t at rt
      subst up
      subst vp
      change (⟨image c raw uq,some (image c raw p)⟩ : Arm i) = ⟨vq,some t⟩
      change image c raw uq = vq at one
      rw [one,two]

abbrev publicRead (i : Input) (root : i.certified.Atom) :=
  frozen (RingChemicalGraphProof.state i) (origin i root)

private theorem domain {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    {u : Arm i} {j : Fin 8} {n : Fin 3} (h : AtLevel root u j n) (c : Fin 8) :
    (carrierFor c i raw).domain u := by
  obtain ⟨on,_,p,prev,pr,_⟩ := h
  intro t ht
  obtain rfl := Option.some.inj (ht.symm.trans prev)
  exact pr.trans on.symm

open RingRetainedStereoRefinement (priority)

/-- At any common depth along two donor paths, both earlier-stage native
branch priorities agree in full, including their complete deep words. -/
theorem priority_eq {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (u v : Arm i) (j k : Fin 8) (n : Fin 3)
    (left : AtLevel root u j n) (right : AtLevel root v k n) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (stage : os = [] ∨ os = [.lowercase])
    {x y : RingStereoSiblingPass.Branch}
    (hu : priority i (publicRead i root) rev os u = some x)
    (hv : priority i (publicRead i root) rev os v = some y) : x = y := by
  let c := carrierFor (choice j k) i raw
  have same := unsignedFor (choice j k) raw ok root zero
  have dest := moved raw root zero u v j k n left right
  have dom := domain raw root left (choice j k)
  rcases stage with rfl|rfl
  · exact c.unit same dom (normalized_unit (RingRetainedStereoRefinement.source [] u hu))
      (dest.symm ▸ normalized_unit (RingRetainedStereoRefinement.source [] v hv))
  · exact c.refinement same [.lowercase] u dom _ _
      (normalized_lower (RingRetainedStereoRefinement.source _ u hu))
      (dest.symm ▸ normalized_lower (RingRetainedStereoRefinement.source _ v hv))

theorem earlier {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (u v : Arm i) (j k : Fin 8) (n : Fin 3)
    (left : AtLevel root u j n) (right : AtLevel root v k n)
    (vu : i.certified.LocalizedRerootCursorValid u) (vv : i.certified.LocalizedRerootCursorValid v) (rev : Bool) :
    ∃ x y, RingFullPathEligibility.key? i (publicRead i root) rev u = some x ∧
      RingFullPathEligibility.key? i (publicRead i root) rev v = some y ∧
      x.throughFourA = y.throughFourA ∧ x.fourC = y.fourC := by
  have ready := RingChemicalGraphProof.ready ok (origin i root)
  obtain ⟨x,hx,ex⟩ := RingFullPathEligibility.key_exact ready rev u vu left.1
  obtain ⟨y,hy,ey⟩ := RingFullPathEligibility.key_exact ready rev v vv right.1
  refine ⟨x,y,hx,hy,?_⟩
  obtain ⟨p,l,ar,as',fr',du,dl,_,_,_,rfl⟩ := (ex x).mpr rfl
  obtain ⟨s,m,br,bs',gr',dv,dm,_,_,_,rfl⟩ := (ey y).mpr rfl
  let c := carrierFor (choice j k) i raw
  have same := unsignedFor (choice j k) raw ok root zero
  have dest := moved raw root zero u v j k n left right
  have dom := domain raw root left (choice j k)
  have unit := c.unit same dom (normalized_unit du) (dest.symm ▸ normalized_unit dv)
  have lower := c.refinement same [.lowercase] u dom _ _ (normalized_lower dl) (dest.symm ▸ normalized_lower dm)
  exact ⟨congrArg RingStereoSiblingPass.Branch.deep unit,congrArg RingStereoSiblingPass.Branch.word lower⟩

theorem root_earlier {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (u v : Fin 4) (a : atom fr u = 1) (b : atom fr v = 2)
    (rev : Bool) :
    ∃ x y, RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr u) = some x ∧
      RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr v) = some y ∧
      x.throughFourA = y.throughFourA ∧ x.fourC = y.fourC := by
  apply earlier raw ok root zero _ _ 0 4 0 _ _ (RingGroupedCentre.valid fr u) (RingGroupedCentre.valid fr v) rev
  · refine ⟨(fr.direction u).property.1,?_,origin i root,rfl,rfl,?_⟩
    · rw [start,a,zero]; rfl
    · change [root.val] = _; rw [zero]; rfl
  · refine ⟨(fr.direction v).property.1,?_,origin i root,rfl,rfl,?_⟩
    · rw [start,b,zero]; rfl
    · change [root.val] = _; rw [zero]; rfl

/-- Match only the three-bond, root-to-donor paths, in newest-first order. -/
def donor? (h : List Nat) := (List.finRange 8).find? fun j => h == route j

private theorem found_all : ∀ j : Fin 8, donor? (route j) = some j := by decide +kernel

open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary

theorem handAt_eq {i : Input} (raw : i.molecule = molecule) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) (q : Arm i) (on : q.occurrence.val.root = root) (rev : Bool) :
    RingFullPathPairs.handAt i (publicRead i root) rev q = (donor? (history q.occurrence)).map
      (fun j => if rev then (hand i.spatial j).swap else hand i.spatial j) := by
  let t := q.occurrence
  let a := RingAllLigandTwoShell.siteAtom i t
  have cur := RingAllLigandTwoShell.site_current i t
  unfold RingFullPathPairs.handAt publicRead
  rw [reader raw ok (origin i root) zero]
  cases found : donor? (history q.occurrence) with
  | none =>
    have outside : ¬ (t.val.node.provenance = .realAtom ∧ 7 ≤ a.val ∧ a.val < 15) := by
      rintro ⟨real,lo,hi⟩
      let j : Fin 8 := ⟨a.val-7,by omega⟩
      have id : a.val = 7+j.val := by dsimp [j]; omega
      have routeEq : history t = route j := CrossParentDonorStore.unique_history raw t
        (congrArg Fin.val on |>.trans zero) real j (by rw [cur]; exact congrArg some id)
      change donor? (history t) = none at found
      rw [routeEq,found_all] at found
      contradiction
    have silent : expectedView t = some none := dif_neg outside
    change RingNestedActivePair.upper (((frozen expectedView (origin i root) t).join).map _) = none
    unfold frozen
    split_ifs <;> first | rfl | rw [silent]; rfl
  | some j =>
    have hr : history t = route j := eq_of_beq (List.find?_some (p := fun j => history t == route j) found)
    obtain ⟨tail,ht,kind⟩ := head_and_kind t cur
    have data : a.val = 7+j.val ∧ tail = [3+j.val/2,1+j.val/4,0] := by
      simpa [route] using ht.symm.trans hr
    have real := kind.mpr (by rw [data.1,data.2]; simp; omega)
    have val : expectedView t = cell (hand i.spatial j) := by
      have good : t.val.node.provenance = .realAtom ∧ 7 ≤ a.val ∧ a.val < 15 :=
        ⟨real,by omega,by omega⟩
      unfold expectedView
      change (if _ : t.val.node.provenance = .realAtom ∧ 7 ≤ a.val ∧ a.val < 15 then _ else _) = _
      rw [dif_pos good]
      congr 2
      apply Fin.ext
      change a.val - 7 = j.val
      omega
    have dist := i.certified.carrierOccurrence_history_length_eq_address_succ t
    have positive : 0 < RingActiveDistanceSchedule.distance t := by
      have len : (history t).length = RingActiveDistanceSchedule.distance t + 1 := by simpa [history,RingActiveDistanceSchedule.distance] using dist
      rw [hr] at len
      change 4 = _ at len
      omega
    have off : t.val.node.current? ≠ some root := fun eqn => by
      have bad := (congrArg Fin.val (Option.some.inj (cur.symm.trans eqn))).trans zero
      omega
    have visible : frozen expectedView (origin i root) t = expectedView t := by
      change (if t.val.root ≠ root then _ else if 0 < RingActiveDistanceSchedule.distance t ∧ _ then _ else _) = _
      rw [if_neg (not_not_intro on),if_pos ⟨positive,off⟩]
    change RingNestedActivePair.upper (((frozen expectedView (origin i root) t).join).map _) = _
    rw [visible,val]
    cases rev <;> rfl

theorem handAt_level {i : Input} (raw : i.molecule = molecule) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) (q : Arm i) (j : Fin 8) (n : Fin 3)
    (here : AtLevel root q j n) (rev : Bool) :
    RingFullPathPairs.handAt i (publicRead i root) rev q =
      if n.val = 2 then some (if rev then (hand i.spatial j).swap else hand i.spatial j) else none := by
  have shape : ∀ (j : Fin 8) (n : Fin 3), donor? (prefixHistory j n) =
      if n.val = 2 then some j else none := by decide +kernel
  rw [handAt_eq raw ok root zero q here.1 rev,here.2.1,shape]
  by_cases eqn : n.val = 2 <;> simp [eqn]

open private atIndex bonds from TetraStereo.Examples.CrossParentDonorStore

/-- Each of the eight measured hands is attained at its own three-bond
occurrence on every admitted geometry of the explicit graph. -/
theorem observed {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (j : Fin 8) :
    ∃ q : Site i, q.val.root = root ∧ history q = route j ∧
      RingChemicalGraphProof.state i q = cell (hand i.spatial j) := by
  let arm := atIndex i graph ⟨1+j.val/4,by omega⟩
  let par := atIndex i graph ⟨3+j.val/2,by omega⟩
  let leaf := atIndex i graph ⟨7+j.val,by omega⟩
  obtain ⟨b1,b2,b3⟩ := bonds j
  have adj {a b : Fin 41} (edge : 0 < molecule.bondOrder a.val b.val) :
      i.certified.moleculeGraph.Adj (atIndex i graph a) (atIndex i graph b) := by
    apply (raw_adj i _ _).mpr
    rwa [graph]
  have rootAt : root = atIndex i graph 0 := Fin.ext zero
  have r0 := zero
  have r1 : arm.val = 1+j.val/4 := rfl
  have r2 : par.val = 3+j.val/2 := rfl
  have r3 : leaf.val = 7+j.val := rfl
  have p : RingGraphPaths.Path i root [leaf,par,arm,root] leaf := by
    refine .step (.step (.step .origin
      (rootAt ▸ adj (a := 0) (b := ⟨1+j.val/4,by omega⟩) b1) ?_)
      (adj (a := ⟨1+j.val/4,by omega⟩) (b := ⟨3+j.val/2,by omega⟩) b2) ?_)
      (adj (a := ⟨3+j.val/2,by omega⟩) (b := ⟨7+j.val,by omega⟩) b3) ?_
    all_goals (simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,r0,r1,r2,r3]; omega)
  let q := RingGraphPaths.site p
  obtain ⟨same,hist,real,cur⟩ := RingGraphPaths.represents_site p
  exact ⟨q,same,by unfold history; rw [hist]; simp [route,r0,r1,r2,r3],public_leaf graph ok q leaf j rfl real cur⟩

end TetraStereo.Examples.CrossParentClasses
assert_kernel_only TetraStereo.Examples.CrossParentClasses.reader
assert_kernel_only TetraStereo.Examples.CrossParentClasses.priority_eq
assert_kernel_only TetraStereo.Examples.CrossParentClasses.earlier
assert_kernel_only TetraStereo.Examples.CrossParentClasses.root_earlier
assert_kernel_only TetraStereo.Examples.CrossParentClasses.handAt_eq
assert_kernel_only TetraStereo.Examples.CrossParentClasses.handAt_level
assert_kernel_only TetraStereo.Examples.CrossParentClasses.observed
