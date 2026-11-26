import TetraStereo.Engine.RingSecondShellDecision
import TetraStereo.Engine.RingPyramidalEarly

/-! The first two atomic-number spheres suffice for many three-ligand pyramids.
Use the occurrence's provenance to distinguish a real neighbor from a terminal
ring duplicate, including at auxiliary centers reached from another root. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalTwoShell
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Labels)
open RingPyramidalSource (Directions slots atomId)
open RingRetainedChemicalPreorder (Direction keyFor read_key orderWord)
attribute [local instance] lexOrd
open private nodup_injective from TetraStereo.Engine.RingPyramidalSource

def direction {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) : Direction i q :=
  ⟨(d.arm s).occurrence,by
    let cursor : Arm i := ⟨q,none⟩
    have present : d.arm s ∈ i.certified.executableLocalizedRerootChildren cursor := d.mem s
    have belongs := List.mem_map_of_mem (f := fun (c : Arm i) => c.occurrence.val) present
    rw [i.certified.executableLocalizedRerootChildren_map cursor] at belongs
    exact ((i.certified.mem_localizedRerootNeighborFrames_iff q.val _).mp
      (i.certified.mem_localizedRerootNeighborFrames_of_mem_intended cursor _ belongs)).2⟩

private theorem arm_eq {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) :
    d.arm s = ⟨(direction d s).val,some q⟩ := by
  have prev := (i.certified.executableLocalizedRerootChildren_declarative
    (⟨q,none⟩ : Arm i)).2 (d.arm s) (d.mem s)
  cases h : d.arm s with
  | mk x p => simpa [direction,h] using prev

def score {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) :=
  RingSecondShellDecision.prefixFor i q (direction d s)

/-- A successful check contains a complete answer, including a flat-frame refusal. -/
def direct? (i : Input) (q : Site i) : Option (Option Labels) := do
  let a ← RingPyramidalPublication.focusP i q
  let d ← RingPyramidalEarly.directions? i q
  let w := score d
  if [w 0,w 1,w 2].Nodup then
    let row := RingStereoSiblingPass.order w slots
    return (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      (row.map (atomId d) ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)
  else none

theorem sound {i : Input} {q : Site i} {v : Option Labels}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (hit : direct? i q = some v) :
    RingChemicalGraphProof.state i q = some v := by
  simp only [direct?,bind,Option.bind_eq_some_iff] at hit
  obtain ⟨a,selected,d,_,tail⟩ := hit
  split at tail <;> try contradiction
  rename_i distinct
  let cs (s : Fin 3) := keyFor (direction d s)
  have native (s : Fin 3) : RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s) := by
    rw [arm_eq d s]
    exact read_key _
  have lower {s t : Fin 3} (lt : score d s < score d t) : orderWord (cs s) < orderWord (cs t) := by
    apply RingAllLigandTwoShell.word_lt_of_prefix
    simpa only [score,RingSecondShellDecision.prefixFor_physical] using lt
  have diff := (nodup_injective (score d)).mp distinct
  have strict : Function.Injective (fun s => orderWord (cs s)) := by
    intro s t eqn
    by_contra ne
    rcases lt_or_gt_of_ne (diff.ne ne) with lt | lt
    · exact (ne_of_lt (lower lt)) eqn
    · exact (ne_of_lt (lower lt)) eqn.symm
  have legal := RingStereoSiblingPass.legal_order (score d) slots
  have size : (RingStereoSiblingPass.order (score d) slots).length = 3 := legal.perm.length_eq
  obtain ⟨j,k,l,row⟩ := List.length_eq_three.mp size
  rw [row] at legal tail
  have nd : [j,k,l].Nodup := legal.perm.nodup_iff.mpr (by decide)
  have sorted : RingStereoSiblingPass.Legal (fun s => orderWord (cs s)) slots [j,k,l] :=
    ⟨legal.perm,List.pairwise_map.mpr (((List.pairwise_map.mp legal.descending).and nd).imp
      (fun h => le_of_lt (lower (lt_of_le_of_ne h.1 (diff.ne h.2.symm)))))⟩
  rw [RingChemicalGraphProof.state_eq]
  simp only [RingPyramidalPublication.publish,selected]
  rw [RingPyramidalConstitution.pLabels_strict d (RingChemicalGraphProof.ready geom q) a cs native strict j k l sorted]
  congr 1
  simpa only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,pure,Option.some.injEq] using tail

open RingGroupedReport (origin)
open RingAtomicNeighborOrder (neighbors)
open RingSecondShellDecision (signature)
open private direction_rank from TetraStereo.Engine.RingPyramidalConstitution

/-- At the original root each direction enters a fresh real neighbor. -/
theorem root_score {i : Input} {a : i.certified.Atom} (d : Directions i (origin i a)) (s : Fin 3) :
    score d s = signature i.molecule a.val (atomId d s) := by
  let q := origin i a
  let u := d.arm s
  have adjacent := (direction d s).property
  have frames := (i.certified.mem_localizedRerootNeighborFrames_iff q.val u.occurrence.val).mpr
    ⟨u.occurrence.property,adjacent⟩
  rw [localizedRerootNeighborFrames,List.mem_append] at frames
  have outward : u.occurrence.val ∈ i.certified.localizedCarrierOutwardChildFrames
      (fuel := i.certified.certified.input.molecule.atomCount+1) q.val := by
    rcases frames with parent | child
    · have test := (List.mem_filter.mp parent).2
      simp only [Bool.and_eq_true,beq_iff_eq] at test
      have len := test.1.2
      change u.occurrence.val.address.length + 1 = 0 at len
      omega
    · exact child
  obtain ⟨w,_,node,_,_,_,_,_,neighbor⟩ :=
    i.certified.simpleBond_outwardFrame_extend_zero i.single q (oAtom := a) rfl rfl _ outward
  have diff : w ≠ a := by
    intro eqn
    exact Nat.lt_irrefl 0 (by simpa only [eqn,MoleculeGraph.Adj,i.certified.moleculeGraph.bond_self] using neighbor)
  have fresh : w ∉ q.val.node.history := by
    change w ∉ [a]
    simpa using diff
  have real : u.occurrence.val.node.provenance = .realAtom := by
    rw [node]
    exact OfficialCIPNode.childProvenance_real q.val.node w fresh
  have atAtom := d.real s
  change u.occurrence.val.node.current? = some (d.atom s) at atAtom
  simp only [score,RingSecondShellDecision.prefixFor,direction,RingAllLigandTwoShell.siteAtom,
    RingSecondShellDecision.signature,atomId]
  change [[RingAtomicNeighborOrder.atomicNumber i.molecule
      (u.occurrence.val.node.current?.getD u.occurrence.val.root).val],
    if u.occurrence.val.node.provenance = .realAtom then _ else []] = _
  simp only [atAtom,d.real s,Option.getD_some,real,if_true]
  rfl

/-- Any selected occurrence whose three actual scores equal the physical
two-shell signatures reads the same strict graph order. -/
theorem state_of_graph_order {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} (a : i.certified.Atom) (focus : RingPyramidalPublication.focusP i q = some a)
    (d : Directions i q) (scores : ∀ s, score d s = signature i.molecule a.val (atomId d s))
    (row : List Nat) (perm : (neighbors i.molecule a.val).Perm row)
    (strict : (row.map (signature i.molecule a.val)).Pairwise (· > ·)) :
    RingChemicalGraphProof.state i q = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        (row ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)) := by
  have sel := RingPhysicalFrameBridge.focusP_phosphorus focus
  simp only [RingPyramidalPublication.phosphorus,Bool.and_eq_true,decide_eq_true_eq] at sel
  have size := (RingAtomicNeighborOrder.degree_eq i a).symm.trans sel.2
  let enum := RingAtomicNeighborOrder.enumeration i a size
  obtain ⟨e,matched⟩ := direction_rank d focus enum
  have ids : (slots.map (atomId d)).Perm row := by
    have p := (Equiv.Perm.map_finRange_perm e).map (fun s => (enum s).val.val)
    rw [List.map_map] at p
    have keyEq : atomId d = fun s => (enum (e s)).val.val := funext fun s => congrArg Fin.val (matched s)
    rw [keyEq]
    exact p.trans ((RingAtomicNeighborOrder.enumeration_ids i a size) ▸ perm)
  let f := signature i.molecule a.val
  have scoreEq : score d = f ∘ atomId d := funext scores
  have all := ids.map f
  rw [List.map_map,←scoreEq] at all
  have nd := all.nodup_iff.mpr (strict.imp (fun h => ne_of_gt h))
  change [score d 0,score d 1,score d 2].Nodup at nd
  have leg := RingStereoSiblingPass.legal_order (score d) slots
  let xs := RingStereoSiblingPass.order (score d) slots
  have shuffled : (xs.map (atomId d)).Perm row := (leg.perm.map _).trans ids
  have desc : ((xs.map (atomId d)).map f).Pairwise (· > ·) := by
    have nd' := (shuffled.map f).nodup_iff.mpr (strict.imp (fun h => ne_of_gt h))
    rw [List.map_map,←scoreEq] at nd' ⊢
    exact (leg.descending.and nd').imp fun h => lt_of_le_of_ne h.1 h.2.symm
  have actual : xs.map (atomId d) = row :=
    List.Perm.eq_of_pairwise (le := fun x y => f y < f x) (fun _ _ _ _ ab ba => (lt_asymm ab ba).elim)
      (List.pairwise_map.mp desc) (List.pairwise_map.mp strict) shuffled
  have hit : direct? i q = some ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        (row ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)) := by
    simp only [direct?,focus,RingPyramidalEarly.directions_of i q d,Option.bind_some,bind,nd,if_true]
    rw [show (RingStereoSiblingPass.order (score d) slots).map (atomId d) = row from actual]
    rfl
  exact sound geom hit

/-- Any graph row whose three two-shell signatures strictly descend gives the
actual pyramidal root response, directly from four physical coordinates. -/
theorem root_of_graph_order {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (selected : RingPyramidalPublication.phosphorus i a = true)
    (row : List Nat) (perm : (neighbors i.molecule a.val).Perm row)
    (strict : (row.map (signature i.molecule a.val)).Pairwise (· > ·)) :
    RingChemicalGraphProof.root i a = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        (row ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)) := by
  let q := origin i a
  have focus : RingPyramidalPublication.focusP i q = some a := by
    have real : q.val.node.provenance = .realAtom := rfl
    have current : q.val.node.current? = some a := rfl
    simp [RingPyramidalPublication.focusP,real,current,selected]
  obtain ⟨d⟩ := RingPyramidalSource.selected_framed focus
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
  exact state_of_graph_order geom a focus d (root_score d) row perm strict

/-- At an original root use the literal bond table before constructing any
occurrence tree. A strict row also settles a coplanar refusal. -/
def rootDecision? (i : Input) (a : i.certified.Atom) : Option (Option Labels) := do
  guard (RingPyramidalPublication.phosphorus i a)
  let key := signature i.molecule a.val
  let row := RingStereoSiblingPass.order key (neighbors i.molecule a.val)
  guard ((row.map key).Pairwise (· > ·))
  return (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (row ++ [a.val])).map
    fun h => (.chiral h,.chiral h.swap)

theorem rootDecision_sound {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) {v : Option Labels} (hit : rootDecision? i a = some v) :
    RingChemicalGraphProof.root i a = some v := by
  let key := signature i.molecule a.val
  let row := RingStereoSiblingPass.order key (neighbors i.molecule a.val)
  by_cases sel : RingPyramidalPublication.phosphorus i a = true
  · by_cases desc : (row.map key).Pairwise (· > ·)
    · have actual := root_of_graph_order geom a sel row
        (RingStereoSiblingPass.legal_order key (neighbors i.molecule a.val)).perm.symm desc
      dsimp only [row,key] at desc actual
      simp only [rootDecision?,sel,guard,desc,if_true,bind,Option.bind,pure] at hit
      exact actual.trans hit
    · dsimp only [row,key] at desc
      simp [rootDecision?,sel,guard,desc] at hit
  · simp [rootDecision?,sel,guard] at hit

end TetraStereo.Engine.RingPyramidalTwoShell
assert_kernel_only TetraStereo.Engine.RingPyramidalTwoShell.sound
assert_kernel_only TetraStereo.Engine.RingPyramidalTwoShell.root_of_graph_order
assert_kernel_only TetraStereo.Engine.RingPyramidalTwoShell.rootDecision_sound
