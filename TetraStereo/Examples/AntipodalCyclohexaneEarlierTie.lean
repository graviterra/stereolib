import TetraStereo.Examples.AntipodalCyclohexaneStore
import TetraStereo.Examples.DecalinEarlierTie

/-! Reflection in the two substituted carbons exchanges the cyclic arms.
It preserves every constitutional observation and every normalized auxiliary
label, even though it reverses the signed hand at the opposite donor. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneEarlierTie
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingGroupedReport (origin)
open RingActiveDistanceSchedule (frozen)
open DecalinAuxiliary (history)
open AntipodalCyclohexaneHands (molecule route)
open AntipodalCyclohexaneStore (store cell frozen_exact)
open RingSplitLigandTie (markingReader normalize)
open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
open private site_eq start normalized_long erase normalized_frozen from TetraStereo.Examples.DecalinEarlierTie
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

def exchange : Nat → Nat
  | 1 => 5 | 5 => 1 | 2 => 4 | 4 => 2
  | 9 => 18 | 18 => 9 | 10 => 19 | 19 => 10
  | 11 => 16 | 16 => 11 | 12 => 17 | 17 => 12 | n => n

private theorem eq_size (i : Input) (raw : i.molecule = molecule) : RingSpatialTransport.size i = 20 := by
  rw [RingSpatialTransport.size,i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,raw]; rfl

private theorem graph : ∀ a : Fin 20, exchange a.val < 20 ∧ exchange (exchange a.val) = a.val ∧
    molecule.atoms[exchange a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : Fin 20, molecule.bondOrder (exchange a.val) (exchange b.val) = molecule.bondOrder a.val b.val := by
  decide +kernel

private def index (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) : Fin 20 :=
  ⟨a.val,by rw [←eq_size i raw]; exact a.isLt⟩

private def perm (i : Input) (raw : i.molecule = molecule) : Equiv.Perm i.certified.Atom :=
  let f (a : i.certified.Atom) : i.certified.Atom := ⟨exchange a.val,by
    change exchange a.val < RingSpatialTransport.size i
    rw [eq_size i raw]
    exact (graph (index i raw a)).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (graph (index i raw a)).2.1
  ⟨f,f,inv,inv⟩

private theorem data : ∀ a : Fin 20,
    molecule.atomZAt (exchange a.val) = molecule.atomZAt a.val ∧
    molecule.atomMassAt (exchange a.val) = molecule.atomMassAt a.val := by decide +kernel

private def aut (i : Input) (raw : i.molecule = molecule) : i.certified.moleculeGraph.Aut := by
  let e := perm i raw
  have phys := LocalizedMarkedCertifiedTerminalRefusal.raw_atom_data i.molecule i.certified i.agreement
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a
    rw [(phys _).1,(phys a).1,raw]
    exact (data (index i raw a)).1
  · intro a
    rw [(phys _).2,(phys a).2,raw]
    exact (data (index i raw a)).2
  · obtain ⟨k,hk⟩ := i.charge
    exact fun a => (hk _).trans (hk a).symm
  · intro a b
    have em : i.certified.moleculeGraph.Adj (e a) (e b) ↔ i.certified.moleculeGraph.Adj a b := by
      rw [raw_adj,raw_adj,raw]
      change 0 < molecule.bondOrder (exchange a.val) (exchange b.val) ↔ _
      exact iff_of_eq (congrArg (fun z => 0 < z) ((graph (index i raw a)).2.2.2 (index i raw b)))
    by_cases h : i.certified.moleculeGraph.Adj a b
    · rw [i.single _ _ (em.mpr h),i.single _ _ h]
    · have h' := mt em.mp h
      exact (Nat.eq_zero_of_not_pos h').trans (Nat.eq_zero_of_not_pos h).symm

private theorem records (i : Input) (raw : i.molecule = molecule) :
    RingGeometryAutomorphism.Records (aut i raw) := by
  intro a
  change i.molecule.atoms[exchange a.val]? = _
  rw [raw]
  exact (graph (index i raw a)).2.2.1

noncomputable def carrier (i : Input) (raw : i.molecule = molecule) :=
  RingGeometryAutomorphism.carrier (aut i raw) (records i raw)

private def image {i : Input} (raw : i.molecule = molecule) (q : Site i) : Site i :=
  RingGeometryAutomorphism.site (aut i raw) q

private theorem image_history {i : Input} (raw : i.molecule = molecule) (q : Site i) :
    history (image raw q) = (history q).map exchange := by
  simp only [history,image,RingGeometryAutomorphism.site,transportOccurrence_node,mapOfficialNode,
    List.map_map]
  rfl

private theorem fixed {i : Input} (raw : i.molecule = molecule) {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) : (aut i raw).val root = root := by
  apply Fin.ext
  change exchange root.val = root.val
  rw [atRoot]
  fin_cases r <;> rfl

private theorem image_root {i : Input} (raw : i.molecule = molecule) {q : Site i} {root : i.certified.Atom}
    (r : Fin 2) (atRoot : root.val = 3*r.val) (on : q.val.root = root) : (image raw q).val.root = root := by
  change (aut i raw).val q.val.root = root
  rw [on,fixed raw r atRoot]

private theorem origin_fixed {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) : image raw (origin i root) = origin i root := by
  apply site_eq (image_root raw r atRoot rfl)
  rw [image_history]
  change [exchange root.val] = [root.val]
  exact congrArg (fun n : Nat => [n]) (congrArg Fin.val (fixed raw r atRoot))

private theorem route_swap (r : Fin 2) :
    (route r 0).map exchange = route r 1 ∧ (route r 1).map exchange = route r 0 := by
  fin_cases r <;> decide

private theorem erase_store {i : Input} (raw : i.molecule = molecule) (r : Fin 2) (q : Site i) :
    erase (store i r q) = erase (store i r (image raw q)) := by
  have inv : ((history q).map exchange).map exchange = history q := by
    unfold history
    simp only [List.map_map]
    conv_rhs => rw [←List.map_id (q.val.node.history.map Fin.val),List.map_map]
    apply List.map_congr_left
    intro a _
    exact (graph (index i raw a)).2.1
  obtain ⟨lr,rl⟩ := route_swap r
  have im := image_history raw q
  have left : history (image raw q) = route r 0 ↔ history q = route r 1 :=
    ⟨fun h => inv.symm.trans (by rw [←im,h,lr]),fun h => im.trans (by rw [h,rl])⟩
  have right : history (image raw q) = route r 1 ↔ history q = route r 0 :=
    ⟨fun h => inv.symm.trans (by rw [←im,h,rl]),fun h => im.trans (by rw [h,lr])⟩
  have diff : route r 0 ≠ route r 1 := by fin_cases r <;> decide
  have eqc : erase (cell i r 0) = erase (cell i r 1) := congrArg some (normalized_long _)
  by_cases l : history q = route r 0
  · have n : history q ≠ route r 1 := fun h => diff (l.symm.trans h)
    simpa only [store,left,right,if_pos l,if_neg n] using eqc
  by_cases rr : history q = route r 1
  · simpa only [store,left,right,if_pos rr,if_neg l] using eqc.symm
  simp only [store,left,right,if_neg rr,if_neg l]

theorem exchange_frozen {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (r : Fin 2) (atRoot : root.val = 3*r.val) :
    let read := markingReader (frozen (RingChemicalGraphProof.state i) (origin i root))
    RingGeometryExchange.Frozen (carrier i raw) read read := by
  dsimp only
  rw [frozen_exact raw ok r atRoot]
  intro q _
  rw [normalized_frozen,normalized_frozen]
  have h := RingGeometryAutomorphism.frozen_transport (aut i raw) (origin i root) q.occurrence
    (s := fun t => erase (store i r t)) (t := fun t => erase (store i r t)) (fun v _ => erase_store raw r v)
  change _ = frozen _ (image raw (origin i root)) (image raw q.occurrence) at h
  rwa [origin_fixed raw root r atRoot] at h

open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)

theorem exchange_slot {i : Input} (raw : i.molecule = molecule)
    (root : i.certified.Atom) (r : Fin 2) (atRoot : root.val = 3*r.val)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange (atom fr a) = atom fr b) :
    (carrier i raw).image (cursor fr a) = cursor fr b := by
  have orig := origin_fixed raw root r atRoot
  have here : image raw (cursor fr a).occurrence = (cursor fr b).occurrence := by
    apply site_eq
    · exact (image_root raw r atRoot (fr.direction a).property.1).trans (fr.direction b).property.1.symm
    · rw [image_history,start,start]
      simp [matchId,show exchange root.val = root.val from congrArg Fin.val (fixed raw r atRoot)]
  change (⟨image raw (cursor fr a).occurrence,some (image raw (origin i root))⟩ : Arm i) = _
  rw [here,orig]
  rfl

/-- Rule 1 through Rule 4a and the lowercase Rule 4c word coincide on
exchanged arms, including the two ring paths at either substituted carbon. -/
theorem earlier {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (r : Fin 2) (atRoot : root.val = 3*r.val)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange (atom fr a) = atom fr b) (rev : Bool) :
    let read := frozen (RingChemicalGraphProof.state i) (origin i root)
    ∃ x y, RingFullPathEligibility.key? i read rev (cursor fr a) = some x ∧
      RingFullPathEligibility.key? i read rev (cursor fr b) = some y ∧
      x.throughFourA = y.throughFourA ∧ x.fourC = y.fourC := by
  let read := frozen (RingChemicalGraphProof.state i) (origin i root)
  have ready := RingChemicalGraphProof.ready ok (origin i root)
  obtain ⟨x,hx,ex⟩ := RingFullPathEligibility.key_exact ready rev _ (RingGroupedCentre.valid fr a)
    (fr.direction a).property.1
  obtain ⟨y,hy,ey⟩ := RingFullPathEligibility.key_exact ready rev _ (RingGroupedCentre.valid fr b)
    (fr.direction b).property.1
  refine ⟨x,y,hx,hy,?_⟩
  obtain ⟨u,l,ar,as',fr',du,dl,_,_,_,rfl⟩ := (ex x).mpr rfl
  obtain ⟨v,m,br,bs',gr',dv,dm,_,_,_,rfl⟩ := (ey y).mpr rfl
  let c := carrier i raw
  have dom : c.domain (cursor fr a) := by
    intro p hp
    obtain rfl := Option.some.inj hp
    exact (fr.direction a).property.1.symm
  have dest := exchange_slot raw root r atRoot fr a b matchId
  have same := exchange_frozen raw ok root r atRoot
  have unit := c.unit same dom (normalized_unit du) (dest.symm ▸ normalized_unit dv)
  have lower := c.refinement same [.lowercase] (cursor fr a) dom _ _
    (normalized_lower dl) (dest.symm ▸ normalized_lower dm)
  exact ⟨congrArg RingStereoSiblingPass.Branch.deep unit,congrArg RingStereoSiblingPass.Branch.word lower⟩

end TetraStereo.Examples.AntipodalCyclohexaneEarlierTie
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneEarlierTie.exchange_frozen
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneEarlierTie.earlier
