import TetraStereo.Engine.RingFrameTransport
import TetraStereo.Engine.RingWrittenHydrogenReadings

/-!
# From physical agreement of written placements to frame transport

`RingWrittenPHReadings.PhysicalAgreement i w x` compares raw readbacks on every enumeration of
the four neighbours of a tetrahedral centre and of the three neighbours of a pyramidal
phosphorus. `RingFrameTransport.SiteAgree` compares raw readbacks on the frames met by the
recursive evaluator. This file proves the first implies the second at every occurrence and
combines `represent_all_centers` with `reportG_transport`.

* `written_frame_order`   : a row that is a permutation of an injective `Fin 4` enumeration
                            is that enumeration read through one `Equiv.Perm (Fin 4)`.
* `tetra_site`            : the written frame of a tetrahedral occurrence.
* `phosphorus_site`       : every order of the three retained directions at a phosphorus focus.
* `siteAgree`             : `PhysicalAgreement i w x → ∀ q, SiteAgree i (geometry w) (geometry x) q`.
* `generated_variant_report`, `generated_variant_root` : one generated variant has the report
                            (root) of an arbitrary nondegenerate written placement, for every
                            request on the fixed topology of `i`.

No hypothesis on the hydrogen inventory is added to those of `represent_all_centers`.
-/
set_option autoImplicit false

namespace TetraStereo.Engine.RingPhysicalFrameBridge
open OneCenter RingHydrogenCompletion RingPyramidalChoices
open LocalizedGenericMarkedRecalculation (readback?)
open LocalizedChemicalRing (Input)

/-! ## Lists -/

theorem oriented_false (g : SpatialConfiguration) :
    RingWrittenPHReadings.oriented g false = RingWrittenPHReadings.geometry g := by
  simp [RingWrittenPHReadings.oriented]

theorem filterMap_length_of_some {α β : Type} (k : α → Option β) :
    ∀ xs : List α, (∀ x ∈ xs, ∃ b, k x = some b) → (xs.filterMap k).length = xs.length
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨b,hb⟩ := h x (List.mem_cons.mpr (Or.inl rfl))
    rw [List.filterMap_cons_some hb,List.length_cons,List.length_cons,
      filterMap_length_of_some k xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem three_of_length {α : Type} : ∀ row : List α, row.length = 3 → ∃ a b c, row = [a,b,c]
  | [], h => by
    have h' : (0 : Nat) = 3 := h
    omega
  | [_], h => by
    have h' : (1 : Nat) = 3 := h
    omega
  | [_,_], h => by
    have h' : (2 : Nat) = 3 := h
    omega
  | [a,b,c], _ => ⟨a,b,c,rfl⟩
  | _ :: _ :: _ :: _ :: l, h => by
    have h' : l.length + 4 = 3 := h
    omega

/-- A four-element row that is a permutation of an injective enumeration is that
enumeration read through one permutation of `Fin 4`. -/
theorem written_frame_order (ids : List Nat) (h : 4 = ids.length) (tgt : Fin 4 → Nat)
    (inj : Function.Injective tgt) (perm : ids.Perm ((List.finRange 4).map tgt)) :
    ∃ π : Equiv.Perm (Fin 4),
      (List.finRange 4).map (fun k => ids.get (Fin.cast h k)) =
        RingWrittenPHReadings.order tgt π := by
  have nodup : ids.Nodup := perm.nodup_iff.mpr ((List.nodup_finRange 4).map inj)
  have finj : Function.Injective (fun k : Fin 4 => ids.get (Fin.cast h k)) := by
    intro a b e
    apply Fin.cast_injective h
    exact nodup.get_inj_iff.mp e
  have range : ∀ k : Fin 4, ∃ y, (fun k : Fin 4 => ids.get (Fin.cast h k)) k = tgt y := by
    intro k
    have mem : ids.get (Fin.cast h k) ∈ (List.finRange 4).map tgt :=
      perm.mem_iff.mp (List.get_mem ids (Fin.cast h k))
    obtain ⟨y,_,e⟩ := List.mem_map.mp mem
    exact ⟨y,e.symm⟩
  obtain ⟨π,hπ⟩ := RingPyramidalChoices.exists_perm_of_injective_range_subset
    (fun k : Fin 4 => ids.get (Fin.cast h k)) tgt finj range
  have e0 : ids.get (Fin.cast h 0) = tgt (π 0) := hπ 0
  have e1 : ids.get (Fin.cast h 1) = tgt (π 1) := hπ 1
  have e2 : ids.get (Fin.cast h 2) = tgt (π 2) := hπ 2
  have e3 : ids.get (Fin.cast h 3) = tgt (π 3) := hπ 3
  have canonical : (List.finRange 4).map (fun k => ids.get (Fin.cast h k)) =
      [ids.get (Fin.cast h 0),ids.get (Fin.cast h 1),ids.get (Fin.cast h 2),
        ids.get (Fin.cast h 3)] := rfl
  have read : [ids.get (Fin.cast h 0),ids.get (Fin.cast h 1),ids.get (Fin.cast h 2),
      ids.get (Fin.cast h 3)] = [tgt (π 0),tgt (π 1),tgt (π 2),tgt (π 3)] := by
    rw [e0,e1,e2,e3]
  exact ⟨π,canonical.trans read⟩

/-- Three listed elements that cover a three-element type enumerate it. -/
theorem three_equiv {β : Type} [Fintype β] (card : Fintype.card β = 3) (key : β → Nat)
    (keyInj : Function.Injective key) (r0 r1 r2 : Nat) (n0 n1 n2 : β)
    (e0 : key n0 = r0) (e1 : key n1 = r1) (e2 : key n2 = r2)
    (cover : ∀ b, key b ∈ [r0,r1,r2]) :
    ∃ d : Fin 3 ≃ β, key (d 0) = r0 ∧ key (d 1) = r1 ∧ key (d 2) = r2 := by
  have surj : Function.Surjective (![n0,n1,n2] : Fin 3 → β) := by
    intro b
    rcases List.mem_cons.mp (cover b) with h | rest
    · exact ⟨0,keyInj (e0.trans h.symm)⟩
    rcases List.mem_cons.mp rest with h | rest
    · exact ⟨1,keyInj (e1.trans h.symm)⟩
    rcases List.mem_cons.mp rest with h | rest
    · exact ⟨2,keyInj (e2.trans h.symm)⟩
    · cases rest
  have bij : Function.Bijective (![n0,n1,n2] : Fin 3 → β) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨surj,by rw [Fintype.card_fin]; exact card.symm⟩
  exact ⟨Equiv.ofBijective _ bij,e0,e1,e2⟩

/-! ## Tetrahedral occurrences -/

/-- The written frame of a tetrahedral occurrence is one order of the canonical neighbour
enumeration of its centre, so physical agreement fixes its hand. -/
theorem tetra_site {i : Input} {w x : SpatialConfiguration}
    (pa : RingWrittenPHReadings.PhysicalAgreement i w x) {q : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i q) :
    readback? (RingWrittenPHReadings.geometry w) (fr.atoms (List.finRange 4)) =
      readback? (RingWrittenPHReadings.geometry x) (fr.atoms (List.finRange 4)) := by
  have inj : Function.Injective
      (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) :=
    fun _ _ e => i.certified.canonicalLigandAtom_injective fr.center (Fin.ext e)
  obtain ⟨π,hπ⟩ := written_frame_order fr.ids
    (by simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq.symm)
    (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) inj fr.physical
  have atoms : fr.atoms (List.finRange 4) = RingWrittenPHReadings.order
      (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) π := hπ
  have agree : readback? (RingWrittenPHReadings.geometry w) (RingWrittenPHReadings.order
        (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) π) =
      readback? (RingWrittenPHReadings.geometry x) (RingWrittenPHReadings.order
        (fun k : Fin 4 => (i.certified.canonicalLigandAtom fr.center k).val) π) := by
    have h := pa.tetra fr.center
      (Equiv.ofBijective (i.certified.canonicalLigandNeighbor fr.center)
        (i.certified.canonicalLigandNeighbor_bijective fr.center)) false π
    rw [oriented_false,oriented_false] at h
    exact h
  rw [atoms]
  exact agree

/-! ## Pyramidal phosphorus occurrences -/

theorem focusP_phosphorus {i : Input} {q : RingActivePairs.Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) :
    RingPyramidalPublication.phosphorus i a = true := by
  unfold RingPyramidalPublication.focusP at selected
  split at selected <;> try contradiction
  exact (Option.filter_eq_some_iff.mp selected).2

/-- Every order of the three retained directions at a phosphorus focus, followed by the
phosphorus, is the phantom frame of one enumeration of its three neighbours. -/
theorem phosphorus_site_order {i : Input} (q : RingActivePairs.Site i)
    (a : i.certified.Atom) (hp : RingPyramidalPublication.focusP i q = some a)
    (row : List Nat) (perm : row.Perm (RingFrameTransport.ligandIds i q)) :
    ∃ d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a,
      RingWrittenPHReadings.order (RingPyramidalChoices.phosphorusFrameIds d) 1 = row ++ [a.val] := by
  obtain ⟨bij,cur,len⟩ := RingPyramidalPublication.focusP_neighbors hp
  have ph := focusP_phosphorus hp
  have ok := ph
  simp only [RingPyramidalPublication.phosphorus,Bool.and_eq_true,decide_eq_true_eq] at ok
  have seen : ∀ (t : RingActivePairs.Arm i)
      (ht : t ∈ RingRetainedAuxiliary.frame i.certified q),
      t.occurrence.val.node.current? = some (bij ⟨t,ht⟩).1 := fun t ht => cur ⟨t,ht⟩
  -- The carrier row has three entries.
  have all : ∀ t ∈ RingRetainedAuxiliary.frame i.certified q,
      ∃ b, t.occurrence.val.node.current?.map Fin.val = some b :=
    fun t ht => ⟨(bij ⟨t,ht⟩).1.val,congrArg (Option.map Fin.val) (seen t ht)⟩
  have idsLen : (RingFrameTransport.ligandIds i q).length = 3 :=
    (filterMap_length_of_some
      (fun t : RingActivePairs.Arm i => t.occurrence.val.node.current?.map Fin.val)
      (RingRetainedAuxiliary.frame i.certified q) all).trans len
  -- Every carrier is a neighbour, and every neighbour is a carrier.
  have isNeighbor : ∀ n ∈ RingFrameTransport.ligandIds i q,
      ∃ nb : i.certified.moleculeGraph.Neighbor a, nb.val.val = n := by
    intro n hn
    have hn' : n ∈ (RingRetainedAuxiliary.frame i.certified q).filterMap
        (fun t : RingActivePairs.Arm i => t.occurrence.val.node.current?.map Fin.val) := hn
    obtain ⟨t,ht,e⟩ := List.mem_filterMap.mp hn'
    have e' : t.occurrence.val.node.current?.map Fin.val = some n := e
    have e'' : some (bij ⟨t,ht⟩).1.val = some n :=
      (congrArg (Option.map Fin.val) (seen t ht)).symm.trans e'
    exact ⟨bij ⟨t,ht⟩,Option.some.inj e''⟩
  have allIn : ∀ nb : i.certified.moleculeGraph.Neighbor a,
      nb.val.val ∈ RingFrameTransport.ligandIds i q := by
    intro nb
    have c := cur (bij.symm nb)
    have back : bij (bij.symm nb) = nb := bij.apply_symm_apply nb
    have value : (bij.symm nb).1.occurrence.val.node.current?.map Fin.val = some nb.val.val :=
      congrArg (Option.map Fin.val)
        (c.trans (congrArg (fun z : i.certified.moleculeGraph.Neighbor a => some z.1) back))
    have mem : nb.val.val ∈ (RingRetainedAuxiliary.frame i.certified q).filterMap
        (fun t : RingActivePairs.Arm i => t.occurrence.val.node.current?.map Fin.val) :=
      List.mem_filterMap.mpr ⟨(bij.symm nb).1,(bij.symm nb).2,value⟩
    exact mem
  -- Name the three entries of the supplied order and enumerate the neighbours by it.
  obtain ⟨r0,r1,r2,rfl⟩ := three_of_length row (perm.length_eq.trans idsLen)
  obtain ⟨n0,e0⟩ := isNeighbor r0 (perm.mem_iff.mp (by simp))
  obtain ⟨n1,e1⟩ := isNeighbor r1 (perm.mem_iff.mp (by simp))
  obtain ⟨n2,e2⟩ := isNeighbor r2 (perm.mem_iff.mp (by simp))
  obtain ⟨d,k0,k1,k2⟩ := three_equiv (by convert ok.2)
    (fun nb : i.certified.moleculeGraph.Neighbor a => nb.val.val)
    (fun _ _ e => Subtype.ext (Fin.ext e)) r0 r1 r2 n0 n1 n2 e0 e1 e2
    (fun nb => perm.mem_iff.mpr (allIn nb))
  have d0 : (d 0).val.val = r0 := k0
  have d1 : (d 1).val.val = r1 := k1
  have d2 : (d 2).val.val = r2 := k2
  have raw : RingWrittenPHReadings.order (RingPyramidalChoices.phosphorusFrameIds d) 1 =
      [(d 0).val.val,(d 1).val.val,(d 2).val.val] ++ [a.val] := rfl
  have list : RingWrittenPHReadings.order (RingPyramidalChoices.phosphorusFrameIds d) 1 =
      [r0,r1,r2] ++ [a.val] := by
    rw [raw,d0,d1,d2]
  exact ⟨d,list⟩

theorem phosphorus_site {i : Input} {w x : SpatialConfiguration}
    (pa : RingWrittenPHReadings.PhysicalAgreement i w x) (q : RingActivePairs.Site i)
    (a : i.certified.Atom) (hp : RingPyramidalPublication.focusP i q = some a)
    (row : List Nat) (perm : row.Perm (RingFrameTransport.ligandIds i q)) :
    readback? (RingWrittenPHReadings.geometry w) (row ++ [a.val]) =
      readback? (RingWrittenPHReadings.geometry x) (row ++ [a.val]) := by
  obtain ⟨d,list⟩ := phosphorus_site_order q a hp row perm
  have ph := focusP_phosphorus hp
  have agree := pa.phosphorus a ph d false
  rw [oriented_false,oriented_false,list] at agree
  exact agree

/-! ## Site agreement and the report -/

/-- **Bridge.** Physical agreement of two full coordinate tables gives agreement of the
raw frame readings at every occurrence of the fixed topology. -/
theorem siteAgree {i : Input} {w x : SpatialConfiguration}
    (pa : RingWrittenPHReadings.PhysicalAgreement i w x) (q : RingActivePairs.Site i) :
    RingFrameTransport.SiteAgree i (RingWrittenPHReadings.geometry w)
      (RingWrittenPHReadings.geometry x) q :=
  ⟨fun fr => tetra_site pa fr,fun a hp row perm => phosphorus_site pa q a hp row perm⟩

/-- **One generated variant for every request.** For an arbitrary nondegenerate written
placement of the selected hydrogens there is one enumerated coordinate table whose complete
fixed-topology report equals that of the written placement on every list of requested atoms.
The variant is chosen before the request. -/
theorem generated_variant_report {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : RingWrittenPHReadings.Placement m g out pos w) (cert : Certified m g out pos)
    (i : Input) (same : i.molecule = out) :
    ∃ x ∈ variants m g out pos, ∀ atoms : List i.certified.Atom,
      RingFrameTransport.reportG i (RingWrittenPHReadings.geometry w) atoms =
        RingFrameTransport.reportG i (RingWrittenPHReadings.geometry x) atoms := by
  obtain ⟨x,hx,pa⟩ := RingWrittenPHReadings.represent_all_centers p cert i same
  exact ⟨x,hx,fun atoms =>
    RingFrameTransport.reportG_transport atoms (fun u _ => siteAgree pa u)⟩

/-- The same variant gives every recursive root cell, including refusals and unresolved cells. -/
theorem generated_variant_root {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : RingWrittenPHReadings.Placement m g out pos w) (cert : Certified m g out pos)
    (i : Input) (same : i.molecule = out) :
    ∃ x ∈ variants m g out pos, ∀ a : i.certified.Atom,
      RingFrameTransport.rootG i (RingWrittenPHReadings.geometry w) a =
        RingFrameTransport.rootG i (RingWrittenPHReadings.geometry x) a := by
  obtain ⟨x,hx,pa⟩ := RingWrittenPHReadings.represent_all_centers p cert i same
  exact ⟨x,hx,fun a => RingFrameTransport.rootG_transport a (fun u _ => siteAgree pa u)⟩

end TetraStereo.Engine.RingPhysicalFrameBridge

assert_kernel_only TetraStereo.Engine.RingPhysicalFrameBridge.siteAgree
assert_kernel_only TetraStereo.Engine.RingPhysicalFrameBridge.generated_variant_report
assert_kernel_only TetraStereo.Engine.RingPhysicalFrameBridge.generated_variant_root
