import TetraStereo.Examples.PairedCyclopropylDonorStore
import TetraStereo.Examples.DecalinEarlierTie

/-! The exchange of the two substituted cyclopropyl ligands preserves the
earlier priority fields on the actual frozen root reader at all admitted
geometries. The individual uppercase hands may vary independently. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylEarlierTie
open OneCenter Engine CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (frozen Visible)
open RingGroupedReport (origin)
open DecalinAuxiliary (history)
open PairedCyclopropylPaths (molecule route)
open RingSplitLigandTie (markingReader normalize)
open private site_eq start normalized_frozen erase from TetraStereo.Examples.DecalinEarlierTie
open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

/-- Swap the two eleven-atom ligand blocks, fixing the central carbon, F and H. -/
def exchange (n : Nat) : Nat :=
  if n < 3 then n else if n < 14 then n+11 else n-11

private abbrev ID := Fin 25
private def index (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) : ID :=
  RingHydrogenSpelling.rawVertices i raw a

private theorem graph : ∀ a : ID, exchange a.val < 25 ∧ exchange (exchange a.val) = a.val ∧
    molecule.atoms[exchange a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : ID, molecule.bondOrder (exchange a.val) (exchange b.val) = molecule.bondOrder a.val b.val := by
  decide +kernel

private def perm (i : Input) (raw : i.molecule = molecule) : Equiv.Perm i.certified.Atom :=
  let f (a : i.certified.Atom) := PairedCyclopropylPaths.atom i raw ⟨exchange a.val,(graph (index i raw a)).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (graph (index i raw a)).2.1
  ⟨f,f,inv,inv⟩

private theorem data : ∀ a : ID,
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
    (zero : root.val = 0) : (aut i raw).val root = root := by
  apply Fin.ext
  change exchange root.val = root.val
  rw [zero]
  rfl

private theorem image_root {i : Input} (raw : i.molecule = molecule) {q : Site i} {root : i.certified.Atom}
    (zero : root.val = 0) (on : q.val.root = root) : (image raw q).val.root = root := by
  change (aut i raw).val q.val.root = root
  rw [on,fixed raw zero]

private theorem origin_fixed {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) : image raw (origin i root) = origin i root := by
  apply site_eq (image_root raw zero rfl)
  rw [image_history]
  change [exchange root.val] = [root.val]
  rw [zero]
  rfl

private theorem route_exchange : ∀ side visit, (route side visit).map exchange = route (!side) visit := by
  decide +kernel

private theorem outside {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (zero : root.val = 0) {q : Site i} (vis : Visible (origin i root) q)
    (off : ¬ ∃ s v, history q = route s v) : RingChemicalGraphProof.state i q = some none := by
  by_cases active : RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) q
  · have same : root = PairedCyclopropylPaths.atom i raw 0 := Fin.ext zero
    have on : q.val.root = root := vis.1
    have other : q.val.node.current? ≠ some root := vis.2.2
    obtain hit | twins := PairedCyclopropylPaths.candidate_cases i raw q
      ⟨on.trans same,same ▸ other,active⟩
    · exact (off hit).elim
    · exact RingRootTwinDecision.sound i q ok _ twins
  · rw [RingChemicalGraphProof.state_eq]
    exact RingChemicalGraphProof.skips i q _ active

private theorem visible_erase {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (zero : root.val = 0) (q : Site i) (vis : Visible (origin i root) q) :
    erase (RingChemicalGraphProof.state i q) = erase (RingChemicalGraphProof.state i (image raw q)) := by
  have im := image_history raw q
  by_cases hit : ∃ s v, history q = route s v
  · obtain ⟨s,v,path⟩ := hit
    have there : history (image raw q) = route (!s) v := im.trans (by rw [path,route_exchange])
    obtain ⟨_,_,value⟩ := PairedCyclopropylDonorStore.public_hand raw ok s v path
    obtain ⟨_,_,other⟩ := PairedCyclopropylDonorStore.public_hand raw ok (!s) v there
    rw [value,other]
    rfl
  · have inv : ((history q).map exchange).map exchange = history q := by
      unfold history
      simp only [List.map_map]
      conv_rhs => rw [←List.map_id (q.val.node.history.map Fin.val),List.map_map]
      apply List.map_congr_left
      intro a _
      exact (graph (index i raw a)).2.1
    have off : ¬ ∃ s v, history (image raw q) = route s v := by
      rintro ⟨s,v,path⟩
      exact hit ⟨!s,v,inv.symm.trans (by rw [←im,path,route_exchange])⟩
    have vis' := (RingGeometryAutomorphism.visible (aut i raw) (origin i root) q).mpr vis
    change Visible (image raw (origin i root)) (image raw q) at vis'
    rw [origin_fixed raw root zero] at vis'
    rw [outside raw ok zero vis hit,outside raw ok zero vis' off]

theorem exchange_frozen {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) :
    let read := markingReader (frozen (RingChemicalGraphProof.state i) (origin i root))
    RingGeometryExchange.Frozen (carrier i raw) read read := by
  dsimp only
  intro q _
  rw [normalized_frozen,normalized_frozen]
  have h := RingGeometryAutomorphism.frozen_transport (aut i raw) (origin i root) q.occurrence
    (s := fun t => erase (RingChemicalGraphProof.state i t))
    (t := fun t => erase (RingChemicalGraphProof.state i t)) (visible_erase raw ok root zero)
  change _ = frozen _ (image raw (origin i root)) (image raw q.occurrence) at h
  rwa [origin_fixed raw root zero] at h

open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)

theorem exchange_slot {i : Input} (raw : i.molecule = molecule)
    (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange (atom fr a) = atom fr b) :
    (carrier i raw).image (cursor fr a) = cursor fr b := by
  have orig := origin_fixed raw root zero
  have here : image raw (cursor fr a).occurrence = (cursor fr b).occurrence := by
    apply site_eq
    · exact (image_root raw zero (fr.direction a).property.1).trans (fr.direction b).property.1.symm
    · rw [image_history,start,start]
      simp [matchId,show exchange root.val = root.val from congrArg Fin.val (fixed raw zero)]
  change (⟨image raw (cursor fr a).occurrence,some (image raw (origin i root))⟩ : Arm i) = _
  rw [here,orig]
  rfl

/-- Rule 1 through Rule 4a and the lowercase Rule 4c word coincide on
exchanged arms, including the two cyclopropyl ligands of the central carbon. -/
theorem earlier {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0)
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
  have dest := exchange_slot raw root zero fr a b matchId
  have same := exchange_frozen raw ok root zero
  have unit := c.unit same dom (normalized_unit du) (dest.symm ▸ normalized_unit dv)
  have lower := c.refinement same [.lowercase] (cursor fr a) dom _ _
    (normalized_lower dl) (dest.symm ▸ normalized_lower dm)
  exact ⟨congrArg RingStereoSiblingPass.Branch.deep unit,congrArg RingStereoSiblingPass.Branch.word lower⟩

end TetraStereo.Examples.PairedCyclopropylEarlierTie
assert_kernel_only TetraStereo.Examples.PairedCyclopropylEarlierTie.exchange_frozen
assert_kernel_only TetraStereo.Examples.PairedCyclopropylEarlierTie.earlier
