import TetraStereo.Examples.DecalinAuxiliary
import TetraStereo.Examples.DecalinAuxiliaryInventory
import TetraStereo.Engine.RingSplitLigandTie
import TetraStereo.Engine.RingGeometryAutomorphism
import TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal

/-! Earlier-sequence-rule invariance when the two long decalin arms are exchanged.
The graph permutation need not preserve the coordinate configuration. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinEarlierTie
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (distance frozen Visible)
open RingGroupedReport (origin)
open DecalinFrames (molecule)
open DecalinPathSwap (exchange)
open DecalinAuxiliary (history route)
open DecalinAuxiliaryInventory (routes)
open RingSplitLigandTie (markingReader normalize)
open private graph perm index from TetraStereo.Examples.DecalinPathSwap
open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

private theorem data : ∀ a : Fin 28,
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

private theorem site_eq {i : Input} {q t : Site i} (root : q.val.root = t.val.root)
    (hist : history q = history t) : q = t := by
  have heq : q.val.node.history = t.val.node.history :=
    List.map_injective_iff.mpr Fin.val_injective hist
  apply i.certified.molecularFrameUnit_injective_on_simpleBonded_carrier i.single
  simp [molecularFrameUnit,root,heq]

private theorem fixed {i : Input} (raw : i.molecule = molecule) (j : i.certified.Atom)
    (n : j.val < 2) : (aut i raw).val j = j := by
  apply Fin.ext
  change exchange j.val = j.val
  have e : j.val = 0 ∨ j.val = 1 := by omega
  rcases e with e|e <;> rw [e] <;> rfl

private theorem image_root {i : Input} (raw : i.molecule = molecule)
    {q : Site i} {j : i.certified.Atom} (eq : q.val.root = j) (n : j.val < 2) :
    (image raw q).val.root = j := by
  change (aut i raw).val q.val.root = j
  rw [eq,fixed raw j n]

private theorem route_cases (j : Fin 2) :
    routes j.val = [[1-j.val,j.val],route j 0,route j 1] ∧
    [1-j.val,j.val].map exchange = [1-j.val,j.val] ∧
    (route j 0).map exchange = route j 1 ∧ (route j 1).map exchange = route j 0 := by
  fin_cases j <;> decide +kernel

private theorem normalized_long (g : Option RS) :
    (g.map (fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
      LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap))).map normalize =
    ((g.map RS.swap).map (fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
      LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap))).map normalize := by
  cases g <;> rfl

private def erase (c : RingActiveDistanceSchedule.Cell) := c.map (Option.map normalize)

private theorem visible_erase {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (small : root.val < 2) (q : Site i)
    (v : Visible (origin i root) q) :
    erase (RingChemicalGraphProof.state i q) = erase (RingChemicalGraphProof.state i (image raw q)) := by
  let j : Fin 2 := ⟨root.val,small⟩
  obtain ⟨list,hd,lr,rl⟩ := route_cases j
  have hr : q.val.root = root := v.1
  have hr' := image_root raw hr small
  have im := image_history raw q
  by_cases d : history q = [1-j.val,j.val]
  · have fix := site_eq (hr'.trans hr.symm) (im.trans (by rw [d,hd]))
    rw [fix]
  by_cases l : history q = route j 0
  · have e : history (image raw q) = route j 1 := im.trans (by rw [l,lr])
    rw [DecalinAuxiliary.public_state raw ok j 0 l,DecalinAuxiliary.public_state raw ok j 1 e]
    exact congrArg some (normalized_long _)
  by_cases r : history q = route j 1
  · have e : history (image raw q) = route j 0 := im.trans (by rw [r,rl])
    rw [DecalinAuxiliary.public_state raw ok j 1 r,DecalinAuxiliary.public_state raw ok j 0 e]
    exact congrArg some (normalized_long _).symm
  have off : history q ∉ routes j.val := by simp [list,d,l,r]
  have inv : ((history q).map exchange).map exchange = history q := by
    unfold history
    simp only [List.map_map]
    conv_rhs => rw [←List.map_id (q.val.node.history.map Fin.val),List.map_map]
    apply List.map_congr_left
    intro a _
    exact (graph (index i raw a)).2.1
  have off' : history (image raw q) ∉ routes j.val := by
    rw [list]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro (eq|eq|eq)
    · exact d (inv.symm.trans (by rw [←im,eq,hd]))
    · exact r (inv.symm.trans (by rw [←im,eq,lr]))
    · exact l (inv.symm.trans (by rw [←im,eq,rl]))
  have vi := (RingGeometryAutomorphism.visible (aut i raw) _ _).mpr v
  have other : (image raw q).val.node.current? ≠ some root := by
    have moved := vi.2.2
    change (image raw q).val.node.current? ≠ some (image raw (origin i root)).val.root at moved
    rwa [image_root raw (q := origin i root) rfl small] at moved
  rw [DecalinAuxiliaryInventory.outside raw ok small q hr v.2.2 off,
    DecalinAuxiliaryInventory.outside raw ok small _ hr' other off']

private theorem origin_fixed {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (small : root.val < 2) : image raw (origin i root) = origin i root := by
  apply site_eq (image_root raw rfl small)
  rw [image_history]
  change [exchange root.val] = [root.val]
  exact congrArg (fun n : Nat => [n]) (congrArg Fin.val (fixed raw root small))

private theorem normalized_frozen {i : Input} (s : RingActiveDistanceSchedule.View i)
    (q t : Site i) : markingReader (frozen s q) t = frozen (fun v => erase (s v)) q t := by
  unfold markingReader frozen erase
  split_ifs <;> rfl

theorem exchange_frozen {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (small : root.val < 2) :
    let r := markingReader (frozen (RingChemicalGraphProof.state i) (origin i root))
    RingGeometryExchange.Frozen (carrier i raw) r r := by
  dsimp only
  intro q _
  rw [normalized_frozen,normalized_frozen]
  have h := RingGeometryAutomorphism.frozen_transport (aut i raw) (origin i root) q.occurrence
    (s := fun v => erase (RingChemicalGraphProof.state i v))
    (t := fun v => erase (RingChemicalGraphProof.state i v)) (visible_erase raw ok root small)
  change _ = frozen _ (image raw (origin i root)) (image raw q.occurrence) at h
  rwa [origin_fixed raw root small] at h

open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)

private theorem start {i : Input} (root : i.certified.Atom)
    (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4) :
    history (cursor fr s).occurrence = [atom fr s,root.val] := by
  have present : fr.arm s ∈ i.certified.executableLocalizedRerootChildren
      ⟨origin i root,none⟩ := List.get_mem ..
  obtain ⟨w,atW,h⟩ := DecalinAuxiliary.child_history (a := root) rfl rfl present
  have atId := fr.point_at s
  rw [atW] at atId
  have eq : w.val = atom fr s := Option.some.inj atId
  change history (fr.arm s).occurrence = _
  rw [h]
  change DecalinAuxiliary.advance [root.val] w.val = _
  simp [DecalinAuxiliary.advance,eq]

theorem exchange_slot {i : Input} (raw : i.molecule = molecule)
    (root : i.certified.Atom) (small : root.val < 2)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange (atom fr a) = atom fr b) :
    (carrier i raw).image (cursor fr a) = cursor fr b := by
  have orig := origin_fixed raw root small
  have here : image raw (cursor fr a).occurrence = (cursor fr b).occurrence := by
    apply site_eq
    · exact (image_root raw (fr.direction a).property.1 small).trans (fr.direction b).property.1.symm
    · rw [image_history,start,start]
      simp [matchId,show exchange root.val = root.val from congrArg Fin.val (fixed raw root small)]
  change (⟨image raw (cursor fr a).occurrence,some (image raw (origin i root))⟩ : Arm i) = _
  rw [here,orig]
  rfl

/-- Rule 1 through Rule 4a and the lowercase Rule 4c word coincide on
exchanged arms, including the two four-carbon paths at each fusion root. -/
theorem earlier {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (small : root.val < 2)
    (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4)
    (matchId : exchange (atom fr a) = atom fr b) (rev : Bool) :
    let r := frozen (RingChemicalGraphProof.state i) (origin i root)
    ∃ x y, RingFullPathEligibility.key? i r rev (cursor fr a) = some x ∧
      RingFullPathEligibility.key? i r rev (cursor fr b) = some y ∧
      x.throughFourA = y.throughFourA ∧ x.fourC = y.fourC := by
  let r := frozen (RingChemicalGraphProof.state i) (origin i root)
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
  have dest := exchange_slot raw root small fr a b matchId
  have same := exchange_frozen raw ok root small
  have unit := c.unit same dom (normalized_unit du) (dest.symm ▸ normalized_unit dv)
  have lower := c.refinement same [.lowercase] (cursor fr a) dom _ _
    (normalized_lower dl) (dest.symm ▸ normalized_lower dm)
  exact ⟨congrArg RingStereoSiblingPass.Branch.deep unit,congrArg RingStereoSiblingPass.Branch.word lower⟩

end TetraStereo.Examples.DecalinEarlierTie

assert_kernel_only TetraStereo.Examples.DecalinEarlierTie.earlier
