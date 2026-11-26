import Batteries.Tactic.OpenPrivate
import TetraStereo.Engine.RingBranchSymmetry

/-! Constitutional priorities and physical frames at three-coordinate phosphorus.
The incoming direction at a rerooted occurrence is a physical ligand. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingPyramidalConstitution
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Reader)
open RingPyramidalSource
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
open RingRetainedChemicalTrace (Word)
attribute [local instance] lexOrd
open private trial_order trial_ne key_ne from TetraStereo.Engine.RingFullPathConstitution

/-- Every actual full-path reading extends its executable constitutional key. -/
theorem through_extends {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} {rev : Bool} {s : Fin 3} {key : Key}
    {constitution : RingRetainedChemicalTrace.Key}
    (native : RingRetainedChemicalTrace.key? i (d.arm s) = some constitution)
    (actual : Reads i r rev (d.arm s) key) :
    ∃ suffix : Word, key.throughFourA =
      RingRetainedChemicalPreorder.orderWord constitution ++ [suffix] := by
  obtain ⟨u,l,ar,as',fr,du,_,_,_,_,rfl⟩ := actual
  have unitRead : RingRetainedUnitPass.Reading i r rev (d.arm s) u := du
  obtain ⟨c,hc,prior⟩ := unitRead.constitution
  have same := Option.some.inj (hc.symm.trans native)
  exact ⟨u.word,congrArg (fun prefix' : List Word => prefix' ++ [u.word])
    (prior.trans (congrArg RingRetainedChemicalPreorder.orderWord same))⟩

private theorem ballot {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (constitution : Fin 3 → RingRetainedChemicalTrace.Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (constitution s))
    (strict : Function.Injective (fun s => RingRetainedChemicalPreorder.orderWord (constitution s)))
    (j k l : Fin 3)
    (legal : RingStereoSiblingPass.Legal
      (fun s => RingRetainedChemicalPreorder.orderWord (constitution s)) slots [j,k,l])
    (rev : Bool) :
    ∃ ks : Fin 3 → Key, Ballots d r a rev ks
      [readback? (geometry i rev) [atomId d j,atomId d k,atomId d l,a.val]] := by
  have each (s : Fin 3) := RingFullPathEligibility.key_exact ready rev (d.arm s) (d.valid s) (d.rooted s)
  choose ks got exactKey using each
  have reads (s : Fin 3) : Reads i r rev (d.arm s) (ks s) := (exactKey s _).mpr rfl
  have shape (s : Fin 3) := through_extends d (native s) (reads s)
  let w (s : Fin 3) := trialKey (ks s) []
  have inj : Function.Injective w := by
    intro s t eqn
    by_contra ne
    obtain ⟨u,hu⟩ := shape s
    obtain ⟨v,hv⟩ := shape t
    exact trial_ne hu hv rfl (strict.ne ne) [] [] eqn
  have order (s t : Fin 3) (ne : s ≠ t) :
      w s < w t ↔ RingRetainedChemicalPreorder.orderWord (constitution s) <
        RingRetainedChemicalPreorder.orderWord (constitution t) := by
    obtain ⟨u,hu⟩ := shape s
    obtain ⟨v,hv⟩ := shape t
    exact trial_order hu hv rfl (strict.ne ne) [] []
  have sorted : RingStereoSiblingPass.Legal w slots [j,k,l] := by
    refine ⟨legal.perm,List.pairwise_map.mpr ?_⟩
    have descending := List.pairwise_map.mp legal.descending
    have nd : [j,k,l].Nodup := legal.perm.nodup_iff.mpr (by decide)
    have both := descending.and nd
    exact both.imp (fun {s t} h => le_of_lt ((order t s h.2.symm).mpr
      (lt_of_le_of_ne h.1 (strict.ne h.2.symm))))
  have different : ks 0 ≠ ks 1 := by
    intro eqn
    apply (by decide : (0 : Fin 3) ≠ 1)
    apply inj
    simp only [w,eqn]
  have single : trials ks = [none] := by simp [trials,different]
  refine ⟨ks,reads,?_⟩
  rw [single]
  apply List.Forall₂.cons _ (List.Forall₂.nil)
  refine ⟨fun _ => [],fun _ => rfl,?_⟩
  exact Outcome.read j k l inj sorted ((sense_exact _ _ _ _ _ _).mpr rfl)

/-- Strict native constitutional words force exactly one unmarked physical
trial, on both geometries, at every occurrence with these three directions. -/
theorem pLabels_strict {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (constitution : Fin 3 → RingRetainedChemicalTrace.Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (constitution s))
    (strict : Function.Injective (fun s => RingRetainedChemicalPreorder.orderWord (constitution s)))
    (j k l : Fin 3)
    (legal : RingStereoSiblingPass.Legal
      (fun s => RingRetainedChemicalPreorder.orderWord (constitution s)) slots [j,k,l]) :
    RingPyramidalPublication.pLabels i q r a =
      (readback? (inputGeometry i.certified) [atomId d j,atomId d k,atomId d l,a.val]).map
        (fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  obtain ⟨x,hx⟩ := ballot d ready a constitution native strict j k l legal false
  obtain ⟨y,hy⟩ := ballot d ready a constitution native strict j k l legal true
  have source := (source_iff ready a _).mp (Source.centre d hx hy)
  rw [source]
  clear hx hy source x y
  simp only [geometry,Bool.false_eq_true,if_false,if_true,readback_mirror]
  generalize readback? (inputGeometry i.certified) [atomId d j,atomId d k,atomId d l,a.val] = hand
  cases hand with
  | none => rfl
  | some hand => cases hand <;> rfl
open RingRetainedConstitution (Cursor)
open RingRetainedChemicalTrace

private theorem observation_atomic {i : Input} {d : Nat} {q : Cursor i.certified d}
    {terminal : Bool} {a : i.certified.Atom} {record : AtomSpec} {o : Observation}
    (current : q.occurrence.val.node.current? = some a)
    (written : i.molecule.atoms[a.val]? = some record)
    (hit : observation? i q terminal = some o) : o.atomic = record.element.atomicNumber := by
  unfold observation? at hit
  simp only [current,bind,Option.bind,written] at hit
  simp only [guard,pure] at hit
  split at hit <;> try contradiction
  all_goals
    cases hp : q.occurrence.val.node.provenance <;> simp only [hp] at hit
    all_goals
      cases hm : CIPRule2MassData.rule2MassPico? record.element.atomicNumber record.isotope? <;>
      cases hn : CIPRule2MassData.rule2MassPico? record.element.atomicNumber none <;>
      simp_all
  all_goals try (cases hit; rfl)
  all_goals split at hit <;> simp_all
  all_goals cases hit; rfl

theorem key_atomic {i : Input} {q : RingActivePairs.Arm i}
    {a : i.certified.Atom} {record : AtomSpec} {key : RingRetainedChemicalTrace.Key}
    (current : q.occurrence.val.node.current? = some a)
    (written : i.molecule.atoms[a.val]? = some record)
    (hit : key? i q = some key) : key.root.atomic = record.element.atomicNumber := by
  have source := key_source hit
  cases source with
  | node frame observed lookup complete branches =>
    exact observation_atomic current written observed

theorem word_lt_of_Z {a b : RingRetainedChemicalTrace.Key}
    (va : WellFormed a) (vb : WellFormed b) (lt : a.root.atomic < b.root.atomic) :
    RingRetainedChemicalPreorder.orderWord a < RingRetainedChemicalPreorder.orderWord b := by
  have ha := (va .atomic).2
  have hb := (vb .atomic).2
  simp only [Key.column,Observation.atStage] at ha hb
  change a.atomic.word :: _ < b.atomic.word :: _
  apply List.Lex.rel
  rw [ha,hb]
  apply List.Lex.rel
  exact List.Lex.rel lt

/-- Atomic numbers alone decide a strict three-arm P order. Subsequent isotope,
ring, auxiliary and promotion words cannot override this first coordinate. -/
theorem pLabels_first_Z {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (records : Fin 3 → AtomSpec)
    (written : ∀ s, i.molecule.atoms[(d.atom s).val]? = some (records s))
    (strict : Function.Injective (fun s => (records s).element.atomicNumber))
    (j k l : Fin 3)
    (legal : RingStereoSiblingPass.Legal
      (fun s => (records s).element.atomicNumber) slots [j,k,l]) :
    RingPyramidalPublication.pLabels i q r a =
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        [atomId d j,atomId d k,atomId d l,a.val]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap) := by
  have each (s : Fin 3) := RingFullPathEligibility.key_exact ready false (d.arm s) (d.valid s) (d.rooted s)
  choose ks got exactKey using each
  have source (s : Fin 3) := (exactKey s _).mpr rfl
  have constitution (s : Fin 3) : ∃ c, key? i (d.arm s) = some c := by
    obtain ⟨u,l,ar,as',fr,du,_,_,_,_,_⟩ := source s
    have unitRead : RingRetainedUnitPass.Reading i r false (d.arm s) u := du
    obtain ⟨c,hc,_⟩ := unitRead.constitution
    exact ⟨c,hc⟩
  choose cs native using constitution
  have formed (s : Fin 3) := (key_source (native s)).formed
  have atomic (s : Fin 3) := key_atomic (d.real s) (written s) (native s)
  have lower {s t : Fin 3} (lt : (records s).element.atomicNumber < (records t).element.atomicNumber) :
      RingRetainedChemicalPreorder.orderWord (cs s) < RingRetainedChemicalPreorder.orderWord (cs t) :=
    word_lt_of_Z (formed s) (formed t) (by simpa only [atomic] using lt)
  have inj : Function.Injective (fun s => RingRetainedChemicalPreorder.orderWord (cs s)) := by
    intro s t eqn
    by_contra ne
    rcases lt_or_gt_of_ne (strict.ne ne) with lt | lt
    · exact (ne_of_lt (lower lt)) eqn
    · exact (ne_of_lt (lower lt)) eqn.symm
  have sorted : RingStereoSiblingPass.Legal
      (fun s => RingRetainedChemicalPreorder.orderWord (cs s)) slots [j,k,l] := by
    refine ⟨legal.perm,List.pairwise_map.mpr ?_⟩
    have nd : [j,k,l].Nodup := legal.perm.nodup_iff.mpr (by decide)
    exact ((List.pairwise_map.mp legal.descending).and nd).imp fun h =>
      le_of_lt (lower (lt_of_le_of_ne h.1 (strict.ne h.2.symm)))
  exact pLabels_strict d ready a cs native inj j k l sorted
private theorem direction_rank {i : Input} {q : Site i} (d : Directions i q)
    {a : i.certified.Atom} (selected : RingPyramidalPublication.focusP i q = some a)
    (enum : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) :
    ∃ e : Equiv.Perm (Fin 3), ∀ s, d.atom s = (enum (e s)).val := by
  obtain ⟨bij,physical,_⟩ := RingPyramidalPublication.focusP_neighbors selected
  let f (s : Fin 3) := enum.symm (bij ⟨d.arm s,d.mem s⟩)
  have onto : Function.Surjective f := by
    intro s
    let t := bij.symm (enum s)
    have member : t.val ∈ [d.arm 0,d.arm 1,d.arm 2] := by
      simpa only [d.incident] using t.property
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eqn | eqn | eqn
    · refine ⟨0,?_⟩
      change enum.symm (bij ⟨d.arm 0,d.mem 0⟩) = s
      rw [show (⟨d.arm 0,d.mem 0⟩ : {t // t ∈ RingRetainedAuxiliary.frame i.certified q}) = t
        from Subtype.ext eqn.symm,bij.apply_symm_apply,enum.symm_apply_apply]
    · refine ⟨1,?_⟩
      change enum.symm (bij ⟨d.arm 1,d.mem 1⟩) = s
      rw [show (⟨d.arm 1,d.mem 1⟩ : {t // t ∈ RingRetainedAuxiliary.frame i.certified q}) = t
        from Subtype.ext eqn.symm,bij.apply_symm_apply,enum.symm_apply_apply]
    · refine ⟨2,?_⟩
      change enum.symm (bij ⟨d.arm 2,d.mem 2⟩) = s
      rw [show (⟨d.arm 2,d.mem 2⟩ : {t // t ∈ RingRetainedAuxiliary.frame i.certified q}) = t
        from Subtype.ext eqn.symm,bij.apply_symm_apply,enum.symm_apply_apply]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f ⟨(Finite.injective_iff_surjective).mpr onto,onto⟩
  refine ⟨e,?_⟩
  intro s
  have same := Option.some.inj ((d.real s).symm.trans (physical ⟨d.arm s,d.mem s⟩))
  simpa only [e,Equiv.ofBijective_apply,f,enum.apply_symm_apply] using same

/-- Any selected P with Cl,F,C enumerated in that order has the corresponding
actual physical upper-case labels on every ready reader. -/
theorem pLabels_Cl_F_C {i : Input} {q : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (selected : RingPyramidalPublication.focusP i q = some a)
    (enum : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a)
    (written : ∀ s, i.molecule.atoms[(enum s).val.val]? =
      some (AtomSpec.aliphatic (![Element.Cl,Element.F,Element.C] s))) :
    RingPyramidalPublication.pLabels i q r a =
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        [(enum 0).val.val,(enum 1).val.val,(enum 2).val.val,a.val]).map fun h =>
        (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap) := by
  obtain ⟨d⟩ := selected_framed selected
  obtain ⟨e,ranked⟩ := direction_rank d selected enum
  let recsAt (s : Fin 3) := AtomSpec.aliphatic (![Element.Cl,Element.F,Element.C] (e s))
  have recs (s : Fin 3) : i.molecule.atoms[(d.atom s).val]? = some (recsAt s) := by
    rw [ranked s]
    exact written (e s)
  have zinj : Function.Injective (fun s : Fin 3 =>
      (AtomSpec.aliphatic (![Element.Cl,Element.F,Element.C] s)).element.atomicNumber) := by decide +kernel
  have strict : Function.Injective (fun s => (recsAt s).element.atomicNumber) := zinj.comp e.injective
  have legal : RingStereoSiblingPass.Legal (fun s => (recsAt s).element.atomicNumber)
      slots [e.symm 0,e.symm 1,e.symm 2] := by
    refine ⟨?_,?_⟩
    · exact Equiv.Perm.map_finRange_perm e.symm
    · simp only [List.map_cons,List.map_nil,recsAt,e.apply_symm_apply]
      decide
  have result := pLabels_first_Z d ready a recsAt recs strict
    (e.symm 0) (e.symm 1) (e.symm 2) legal
  have ids (s : Fin 3) : atomId d (e.symm s) = (enum s).val.val := by
    unfold atomId
    rw [ranked,e.apply_symm_apply]
  simpa only [ids] using result

end TetraStereo.Engine.RingPyramidalConstitution
assert_kernel_only TetraStereo.Engine.RingPyramidalConstitution.pLabels_strict

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingWrittenPHReadings RingPyramidalChoices RingNumberedHydrogenGeometry
open LocalizedChemicalRing (Input)

/-- One ordered three-neighbor-plus-center determinant determines all orders and
both reflections, including zero volume and missing-coordinate readings. -/
theorem phosphorus_orders_of_one {i : Input} (w x : SpatialConfiguration)
    (a : i.certified.Atom) (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a)
    (same : readback? (geometry w) (order (phosphorusFrameIds d) 1) =
      readback? (geometry x) (order (phosphorusFrameIds d) 1))
    (other : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a)
    (rev : Bool) (π : Equiv.Perm (Fin 4)) :
    readback? (oriented w rev) (order (phosphorusFrameIds other) π) =
      readback? (oriented x rev) (order (phosphorusFrameIds other) π) := by
  obtain ⟨σ,_,action⟩ := phosphorus_order_reindex other d
  have row : order (phosphorusFrameIds other) π = order (phosphorusFrameIds d) (π.trans σ) := by
    simp only [order,action,Equiv.trans_apply]
  have plain := order_readback_congr (phosphorusFrameIds d) same (π.trans σ)
  rw [←row] at plain
  cases rev <;> simp [oriented,readback_mirror,plain]

/-- Construct branch agreement using any chosen complete neighbor enumeration at
each reachable eligible P. No canonical enumeration, nondegeneracy or output is assumed. -/
theorem branchAgreement_of_phosphorus_orders {i : Input} (c : i.certified.TetrahedralCenter)
    (x : SpatialConfiguration)
    (tetra : ∀ b : i.certified.TetrahedralCenter, b ≠ c → BranchReachable i c.val b.val →
      (¬ ∃ p : TwinPair i, p.c = b) →
      readback? (geometry i.spatial) (RingRetainedAuxiliary.canonical i.certified b) =
        readback? (geometry x) (RingRetainedAuxiliary.canonical i.certified b))
    (chosen : ∀ (a : i.certified.Atom), RingPyramidalPublication.phosphorus i a = true →
      BranchReachable i c.val a → Fin 3 ≃ i.certified.moleculeGraph.Neighbor a)
    (same : ∀ a hp reached,
      readback? (geometry i.spatial) (order (phosphorusFrameIds (chosen a hp reached)) 1) =
        readback? (geometry x) (order (phosphorusFrameIds (chosen a hp reached)) 1)) :
    BranchAgreement i c x := by
  refine ⟨tetra,?_⟩
  intro a hp reached
  exact phosphorus_orders_of_one i.spatial x a (chosen a hp reached) (same a hp reached)
    (phosphorusEnumeration i a hp) false 1

/-- The complete three-neighbor frame as actual atom values, with the P phantom
represented by the supporting P atom in slot 3. -/
def phosphorusFrameAtoms {i : Input} {a : i.certified.Atom}
    (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) : Fin 4 → i.certified.Atom :=
  ![(d 0).val,(d 1).val,(d 2).val,a]

theorem phosphorus_reindexed_order {i : Input} (e : Equiv.Perm i.certified.Atom)
    {a b : i.certified.Atom} (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a)
    (other : Fin 3 ≃ i.certified.moleculeGraph.Neighbor b)
    (action : ∀ k, e.symm (phosphorusFrameAtoms d k) = phosphorusFrameAtoms other k) :
    readback? (geometry (reindexed i i e)) (order (phosphorusFrameIds d) 1) =
      readback? (geometry i.spatial) (order (phosphorusFrameIds other) 1) := by
  have points (k : Fin 4) : geometry (reindexed i i e) (phosphorusFrameIds d k) =
      geometry i.spatial (phosphorusFrameIds other k) := by
    have lookup := reindexed_lookup e (phosphorusFrameAtoms d k)
    rw [action k] at lookup
    fin_cases k <;> exact lookup
  simp only [order,Equiv.Perm.one_apply,readback?,List.mapM_cons,List.mapM_nil,points]
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.phosphorus_orders_of_one
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.branchAgreement_of_phosphorus_orders
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.phosphorus_reindexed_order

assert_kernel_only TetraStereo.Engine.RingPyramidalConstitution.pLabels_first_Z
assert_kernel_only TetraStereo.Engine.RingPyramidalConstitution.pLabels_Cl_F_C
