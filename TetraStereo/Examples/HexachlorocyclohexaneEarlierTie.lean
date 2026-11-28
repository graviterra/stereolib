import TetraStereo.Examples.HexachlorocyclohexanePublicStore
import TetraStereo.Examples.DecalinEarlierTie

/-! Reflection of the six-membered ring about its root preserves all
constitutional columns and the uppercase-unit and lowercase observations. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexaneEarlierTie
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingGroupedReport (origin)
open RingActiveDistanceSchedule (frozen)
open DecalinAuxiliary (history)
open BlueBookHexachlorocyclohexane (exchange molecule)
open HexachlorocyclohexanePublicStore (route tag? carbon)
open private tag_some outside from TetraStereo.Examples.HexachlorocyclohexanePublicStore
open RingSplitLigandTie (markingReader normalize)
open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
open private site_eq start normalized_long erase normalized_frozen from TetraStereo.Examples.DecalinEarlierTie
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

private theorem eq_size (i : Input) (raw : i.molecule = molecule) : RingSpatialTransport.size i = 18 := by
  rw [RingSpatialTransport.size,i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,raw]; rfl

private theorem graph : ∀ (r : Fin 6) (a : Fin 18), exchange r.val a.val < 18 ∧ exchange r.val (exchange r.val a.val) = a.val ∧
    molecule.atoms[exchange r.val a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : Fin 18, molecule.bondOrder (exchange r.val a.val) (exchange r.val b.val) = molecule.bondOrder a.val b.val := by
  decide +kernel

private def index (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) : Fin 18 :=
  ⟨a.val,by rw [←eq_size i raw]; exact a.isLt⟩

private def perm (r : Fin 6) (i : Input) (raw : i.molecule = molecule) : Equiv.Perm i.certified.Atom :=
  let f (a : i.certified.Atom) : i.certified.Atom := ⟨exchange r.val a.val,by
    change exchange r.val a.val < RingSpatialTransport.size i
    rw [eq_size i raw]
    exact (graph r (index i raw a)).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (graph r (index i raw a)).2.1
  ⟨f,f,inv,inv⟩

private theorem data : ∀ (r : Fin 6) (a : Fin 18),
    molecule.atomZAt (exchange r.val a.val) = molecule.atomZAt a.val ∧
    molecule.atomMassAt (exchange r.val a.val) = molecule.atomMassAt a.val := by decide +kernel

private def aut (r : Fin 6) (i : Input) (raw : i.molecule = molecule) : i.certified.moleculeGraph.Aut := by
  let e := perm r i raw
  have phys := LocalizedMarkedCertifiedTerminalRefusal.raw_atom_data i.molecule i.certified i.agreement
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a
    rw [(phys _).1,(phys a).1,raw]
    exact (data r (index i raw a)).1
  · intro a
    rw [(phys _).2,(phys a).2,raw]
    exact (data r (index i raw a)).2
  · obtain ⟨k,hk⟩ := i.charge
    exact fun a => (hk _).trans (hk a).symm
  · intro a b
    have em : i.certified.moleculeGraph.Adj (e a) (e b) ↔ i.certified.moleculeGraph.Adj a b := by
      rw [raw_adj,raw_adj,raw]
      change 0 < molecule.bondOrder (exchange r.val a.val) (exchange r.val b.val) ↔ _
      exact iff_of_eq (congrArg (fun z => 0 < z) ((graph r (index i raw a)).2.2.2 (index i raw b)))
    by_cases h : i.certified.moleculeGraph.Adj a b
    · rw [i.single _ _ (em.mpr h),i.single _ _ h]
    · have h' := mt em.mp h
      exact (Nat.eq_zero_of_not_pos h').trans (Nat.eq_zero_of_not_pos h).symm

private theorem records (r : Fin 6) (i : Input) (raw : i.molecule = molecule) :
    RingGeometryAutomorphism.Records (aut r i raw) := by
  intro a
  change i.molecule.atoms[exchange r.val a.val]? = _
  rw [raw]
  exact (graph r (index i raw a)).2.2.1

noncomputable def carrier (r : Fin 6) (i : Input) (raw : i.molecule = molecule) :=
  RingGeometryAutomorphism.carrier (aut r i raw) (records r i raw)

private def image (r : Fin 6) {i : Input} (raw : i.molecule = molecule) (q : Site i) : Site i :=
  RingGeometryAutomorphism.site (aut r i raw) q

private theorem image_history (r : Fin 6) {i : Input} (raw : i.molecule = molecule) (q : Site i) :
    history (image r raw q) = (history q).map (exchange r.val) := by
  simp only [history,image,RingGeometryAutomorphism.site,transportOccurrence_node,mapOfficialNode,
    List.map_map]
  rfl

private theorem fixed {i : Input} (raw : i.molecule = molecule) {root : i.certified.Atom}
    (r : Fin 6) (atRoot : root.val = r.val) : (aut r i raw).val root = root := by
  apply Fin.ext
  change exchange r.val root.val = root.val
  rw [atRoot]
  fin_cases r <;> rfl

private theorem image_root {i : Input} (raw : i.molecule = molecule) {q : Site i} {root : i.certified.Atom}
    (r : Fin 6) (atRoot : root.val = r.val) (on : q.val.root = root) : (image r raw q).val.root = root := by
  change (aut r i raw).val q.val.root = root
  rw [on,fixed raw r atRoot]

private theorem origin_fixed {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) : image r raw (origin i root) = origin i root := by
  apply site_eq (image_root raw r atRoot rfl)
  rw [image_history]
  change [exchange r.val root.val] = [root.val]
  exact congrArg (fun n : Nat => [n]) (congrArg Fin.val (fixed raw r atRoot))

private theorem route_map : ∀ (r : Fin 6) (cw : Bool) (k : Fin 5),
    (route r cw k).map (exchange r.val) = route r (!cw) k ∧
    tag? r (route r cw k) = some (cw,k) := by decide +kernel

private theorem tagged_image {i : Input} (raw : i.molecule = molecule) (r : Fin 6) (q : Site i) :
    tag? r (history (image r raw q)) = (tag? r (history q)).map (fun t => (!t.1,t.2)) := by
  have im := image_history r raw q
  cases hit : tag? r (history q) with
  | some t =>
    obtain ⟨cw,k⟩ := t
    rw [im,tag_some hit,(route_map r cw k).1,(route_map r (!cw) k).2]
    rfl
  | none =>
    cases h' : tag? r (history (image r raw q)) with
    | none => rfl
    | some t =>
      obtain ⟨cw,k⟩ := t
      have inv : ((history q).map (exchange r.val)).map (exchange r.val) = history q := by
        unfold history
        simp only [List.map_map]
        conv_rhs => rw [←List.map_id (q.val.node.history.map Fin.val),List.map_map]
        apply List.map_congr_left
        intro a _
        exact (graph r (index i raw a)).2.1
      have eq : history q = route r (!cw) k := inv.symm.trans (by rw [←im,tag_some h',(route_map r cw k).1])
      rw [eq,(route_map r (!cw) k).2] at hit
      contradiction

private theorem normalized {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (q : Site i)
    (vis : RingActiveDistanceSchedule.Visible (origin i root) q) :
    erase (RingChemicalGraphProof.state i q) = erase (RingChemicalGraphProof.state i (image r raw q)) := by
  have im := tagged_image raw r q
  cases h : tag? r (history q) with
  | none =>
    rw [h] at im
    have vis' := (RingGeometryAutomorphism.visible (aut r i raw) (origin i root) q).mpr vis
    change RingActiveDistanceSchedule.Visible (image r raw (origin i root)) (image r raw q) at vis'
    rw [origin_fixed raw root r atRoot] at vis'
    rw [outside raw r atRoot q vis.1 vis.2.2 h,
      outside raw r atRoot _ vis'.1 vis'.2.2 im]
  | some t =>
    obtain ⟨cw,k⟩ := t
    rw [h] at im
    have state {q : Site i} {cw : Bool} (here : tag? r (history q) = some (cw,k)) :
        erase (RingChemicalGraphProof.state i q) = some (some (.chiral .R,.chiral .S)) := by
      obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp
        (HexachlorocyclohexanePublicStore.nonflat raw ok ⟨carbon r cw k,Nat.mod_lt _ (by decide)⟩)
      rw [HexachlorocyclohexanePublicStore.public_state raw ok r cw k (tag_some here),hx]
      cases cw <;> rfl
    exact (state h).trans (state (cw := !cw) im).symm

theorem exchange_frozen {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (r : Fin 6) (atRoot : root.val = r.val) :
    let read := markingReader (frozen (RingChemicalGraphProof.state i) (origin i root))
    RingGeometryExchange.Frozen (carrier r i raw) read read := by
  dsimp only
  intro q _
  rw [normalized_frozen,normalized_frozen]
  have h := RingGeometryAutomorphism.frozen_transport (aut r i raw) (origin i root) q.occurrence
    (s := fun t => erase (RingChemicalGraphProof.state i t))
    (t := fun t => erase (RingChemicalGraphProof.state i t)) (normalized raw ok root r atRoot)
  change _ = frozen _ (image r raw (origin i root)) (image r raw q.occurrence) at h
  rwa [origin_fixed raw root r atRoot] at h

open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)

theorem exchange_slot {i : Input} (raw : i.molecule = molecule)
    (root : i.certified.Atom) (r : Fin 6) (atRoot : root.val = r.val)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange r.val (atom fr a) = atom fr b) :
    (carrier r i raw).image (cursor fr a) = cursor fr b := by
  have orig := origin_fixed raw root r atRoot
  have here : image r raw (cursor fr a).occurrence = (cursor fr b).occurrence := by
    apply site_eq
    · exact (image_root raw r atRoot (fr.direction a).property.1).trans (fr.direction b).property.1.symm
    · rw [image_history,start,start]
      simp [matchId,show exchange r.val root.val = root.val from congrArg Fin.val (fixed raw r atRoot)]
  change (⟨image r raw (cursor fr a).occurrence,some (image r raw (origin i root))⟩ : Arm i) = _
  rw [here,orig]
  rfl

/-- Rule 1 through Rule 4a and the lowercase Rule 4c word coincide on
exchanged arms, including the two ring paths at any named carbon. -/
theorem earlier {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (r : Fin 6) (atRoot : root.val = r.val)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange r.val (atom fr a) = atom fr b) (rev : Bool) :
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
  let c := carrier r i raw
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

end TetraStereo.Examples.HexachlorocyclohexaneEarlierTie
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneEarlierTie.exchange_frozen
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexaneEarlierTie.earlier
