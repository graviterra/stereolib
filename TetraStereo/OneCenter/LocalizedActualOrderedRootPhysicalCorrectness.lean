import TetraStereo.OneCenter.LocalizedActualOrderedEvaluatorPreservation
import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalRule4c
import TetraStereo.OneCenter.TrackedLocalizedLigandSortCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000






























namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## Small generic facts -/

/-- A common bound of four numbers. -/
def layoutBound (f : Fin 4 → ℕ) : ℕ := max (max (f 0) (f 1)) (max (f 2) (f 3))

theorem le_layoutBound (f : Fin 4 → ℕ) (i : Fin 4) : f i ≤ layoutBound f := by
  fin_cases i <;> simp [layoutBound]

theorem Ordering.then_of_ne {a : Ordering} (b : Ordering) (h : a ≠ .eq) : a.then b = a := by
  cases a with
  | eq => exact absurd rfl h
  | lt => rfl
  | gt => rfl

/-- Reindexing the canonical enumeration by a permutation is a permutation. -/
theorem finRange_map_perm {n : ℕ} (e : Fin n ≃ Fin n) :
    ((List.finRange n).map e).Perm (List.finRange n) := by
  rw [List.perm_iff_count]
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [List.count_map_of_injective _ _ e.injective,
    List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange _),
    List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange _)]

theorem mapM_map_option {α β γ : Type*} (f : β → Option γ) (g : α → β) :
    ∀ l : List α, (l.map g).mapM f = l.mapM fun a => f (g a)
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, mapM_map_option f g l]

namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The final occurrence of the centre. -/
abbrev top : LocalizedUniversalReference.Occurrence input :=
  ActualReaderPhysicalBranchInverse.topTarget input S.c

/-- The generated reference state's dependency view at the final occurrence. -/
abbrev referenceView : input.certified.LocalizedDependencyView S.top :=
  input.certified.localizedDependencyView (LocalizedUniversalReference.referenceState input) S.top

/-! ## Root readback -/

/-- **Root readback.**  The ordered fixed point at the final occurrence is one ordered root
evaluation on the generated state's view.  No branch-domain or reference-count hypothesis. -/
theorem orderedReferenceState_top_eq_orderedDescriptor :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
      input.certified.localizedOccurrenceRule45DescriptorOrdered? S.top S.referenceView := by
  have deps := orderedReferenceState_eq_referenceState_of_dependency input S.singleBonded S.acyclic
    S.hcharge S.noDouble (input.certified.canonicalReindexConfiguration S.cfg) S.c
    (S.slotSetup 0).globalDomain ⟨S.c.1, S.c.2⟩ rfl
  rw [← input.certified.orderedReferenceState_fixed]
  exact input.certified.localizedExecutableStep_eq_of_depthAgree
    (input.certified.localizedOccurrenceRule45OrderedAuxiliarySemantics
      (LocalizedUniversalReference.carrierFuel input)).executableRule
    _ _ _ fun source hs => deps source hs

/-! ## The ordered pairwise comparison at the root -/

/-- The production compound key of frame slot `i`. -/
abbrev frameKey (i : Fin 4) : input.certified.LocalizedRerootCompoundRule45Key :=
  actualSlotCompoundKey input S.c S.frame S.frameComputed i

theorem slotKey_eq_frameKey (ℓ : Fin 4) : S.slotKey ℓ = S.frameKey (S.slot ℓ) := rfl

theorem compareOrderedAt_top (i j : Fin 4) :
    input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? S.top S.referenceView S.frame
        i j =
      some (localizedOccurrenceRule45ComparisonRecord
        (input.certified.compareLocalizedRerootCompoundThroughRule5
          (input.certified.outcomeOrdered45 (S.frameKey i))
          (input.certified.outcomeOrdered45 (S.frameKey j)))) :=
  input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built S.top S.referenceView
    S.frame (actualSlotCompoundBuilt input S.c S.frame S.frameComputed i)
    (actualSlotCompoundBuilt input S.c S.frame S.frameComputed j)

/-- The ordered through-Rule-5 comparison of the slot keys of two ligands. -/
def orderedRootComparison (ℓ m : Fin 4) : ConstitutionalRule5Comparison :=
  input.certified.compareLocalizedRerootCompoundThroughRule5
    (input.certified.outcomeOrdered45 (S.slotKey ℓ)) (input.certified.outcomeOrdered45 (S.slotKey m))

/-! ## The independent Rules 1–4c priority -/

/-- A chosen stage-`.rule4a` original-root arm of every ligand. -/
def arm4a (ℓ : Fin 4) : input.certified.OriginalRootArm S.center ℓ .rule4a S.read :=
  Classical.choice (input.certified.exists_originalRootArm S.center ℓ .rule4a S.read)

/-- A common layout bounding the four ligand graphs. -/
def layoutWidth : ℕ := layoutBound fun ℓ => (armGraph (S.arm4a ℓ)).width

def layoutHeight : ℕ := layoutBound fun ℓ => (armGraph (S.arm4a ℓ)).height

/-- The independent ligand signature of ligand `ℓ` at the common layout. -/
def signature (ℓ : Fin 4) :=
  ligandSignatureAt input.certified.moleculeGraph (actualReferenceDescriptorMap input)
    (input.certified.topUnit S.center) (armGraph (S.arm4a ℓ)) S.layoutWidth S.layoutHeight

/-- The independent Rules-1–4c comparison of two ligands: the cumulative Rule-4a key
comparison, then the signature comparison. -/
def independentCompare (ℓ m : Fin 4) : Ordering :=
  (input.certified.compareLocalizedRerootCumulativeRule45Keys
    (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey).then
    (signatureCompare (S.signature ℓ) (S.signature m))

/-- C5 at the chosen arms and layout. -/
theorem rule4bc_ordered_eq_signatureCompare {ℓ m : Fin 4}
    (tie4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey = .eq) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
        (input.certified.outcomeOrdered (S.slotKey m).prior) =
      signatureCompare (S.signature ℓ) (S.signature m) :=
  S.compound_eq_signatureCompare (S.arm4a ℓ) (S.arm4a m)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).width) ℓ)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).height) ℓ)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).width) m)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).height) m) tie4a

/-- **The independent priority connection.**  When Rules 1–4c separate two ligands, the ordered
through-Rule-5 comparison of their slot keys is that decision, with no enantiomorphic flag. -/
theorem orderedRootComparison_of_independent_ne {ℓ m : Fin 4}
    (h : S.independentCompare ℓ m ≠ .eq) :
    S.orderedRootComparison ℓ m = { ordering := S.independentCompare ℓ m, pseudo := false } := by
  unfold orderedRootComparison independentCompare at *
  by_cases h4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey = .eq
  · rw [h4a, Ordering.eq_then] at h ⊢
    unfold compareLocalizedRerootCompoundThroughRule5
    simp only [outcomeOrdered45_prior, S.rule4bc_ordered_eq_signatureCompare h4a]
    split_ifs with hc
    · rfl
    · exact absurd (bne_iff_ne.2 h) hc
  · rw [Ordering.then_of_ne _ h4a]
    rw [input.certified.compareThroughRule5_outcomeOrdered45_of_rule4a_ne _ _ h4a]
    unfold compareLocalizedRerootCompoundThroughRule5
    simp only [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne _ _ h4a]
    split_ifs with hc
    · rfl
    · exact absurd (bne_iff_ne.2 h4a) hc

/-! ## Frame slots and ligands -/

/-- The slot/ligand correspondence as an equivalence. -/
def slotEquiv : Fin 4 ≃ Fin 4 := Equiv.ofBijective S.slot S.slot_bijective

theorem slot_slotEquiv_symm (i : Fin 4) : S.slot (S.slotEquiv.symm i) = i :=
  S.slotEquiv.apply_symm_apply i

theorem frameKey_eq_slotKey (i : Fin 4) : S.frameKey i = S.slotKey (S.slotEquiv.symm i) := by
  rw [S.slotKey_eq_frameKey, S.slot_slotEquiv_symm]

/-- The spatial point of a frame slot is the point of its canonical ligand atom. -/
theorem spatialPoint_cursorAt (i : Fin 4) :
    input.certified.localizedRerootCursorSpatialPoint? (S.frame.cursorAt i) =
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom S.center (S.slotEquiv.symm i)) := by
  conv_lhs => rw [← S.slot_slotEquiv_symm i, S.cursorAt_slot]
  rfl

/-! ## The absolute letter -/

/-- **Absolute-letter conclusion.**  If an injective ligand priority realizes the independent
Rules-1–4c comparison on every pair, the ordered evaluator assigns the centre the uppercase letter
read from the oriented volume of the canonical ligand atoms' coordinates in descending priority. -/
theorem orderedReferenceState_top_eq_chiral
    (p : Fin 4 → ℕ) (injective : Function.Injective p)
    (ranked : ∀ ℓ m, ℓ ≠ m → S.independentCompare ℓ m = compare (p ℓ) (p m))
    (order : List (Fin 4)) (perm : order.Perm (List.finRange 4))
    (sorted : order.Pairwise fun a b => p b < p a)
    (points : List CartesianPoint3)
    (hpoints : order.mapM (fun ℓ => input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom S.center ℓ)) = some points)
    (raw : RS) (hraw : descriptorOfPriorityOrderedPoints? points = some raw) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
      some (.chiral raw) := by
  rw [S.orderedReferenceState_top_eq_orderedDescriptor]
  -- the priority transported to frame slots
  let q : Fin 4 → ℕ := fun i => p (S.slotEquiv.symm i)
  have qinj : Function.Injective q := injective.comp S.slotEquiv.symm.injective
  have compared : ∀ i j, i ≠ j →
      input.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? S.top S.referenceView
        S.frame i j = strictRankComparison q i j := by
    intro i j hij
    have hℓm : S.slotEquiv.symm i ≠ S.slotEquiv.symm j :=
      fun h => hij (S.slotEquiv.symm.injective h)
    have decided : S.independentCompare (S.slotEquiv.symm i) (S.slotEquiv.symm j) ≠ .eq := by
      rw [ranked _ _ hℓm]
      exact fun h => hℓm (injective (compare_eq_iff_eq.1 h))
    have record := S.orderedRootComparison_of_independent_ne decided
    unfold orderedRootComparison at record
    rw [S.compareOrderedAt_top, S.frameKey_eq_slotKey i, S.frameKey_eq_slotKey j, record,
      ranked _ _ hℓm]
    rfl
  obtain ⟨tracked, hsort, hperm, hdesc, hzero⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne q qinj _ compared
  have hsafe : input.certified.safeLocalizedOccurrenceRule45TrackedOrderOrdered? S.top
      S.referenceView S.frame = some tracked := by
    unfold safeLocalizedOccurrenceRule45TrackedOrderOrdered? safeTrackedOrderOf
    rw [hsort]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [if_pos]
    rw [orderCoherentOf_eq_true_iff]
    refine hdesc.imp ?_
    intro i j hij
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    refine ⟨_, compared i j hne, ?_⟩
    show compare (q i) (q j) = .gt
    exact compare_gt_iff_gt.2 hij
  have hcenter : input.certified.localizedOccurrenceDescriptorCenter? S.top =
      some ⟨S.c.1, S.c.2⟩ :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff S.top ⟨S.c.1, S.c.2⟩).2
      ⟨input.certified.carrierOccurrence_provenance_real S.singleBonded S.acyclic S.top,
        ActualReaderPhysicalBranchInverse.topTarget_current input S.c⟩
  have hmapEq : tracked.highestFirst.map S.slotEquiv.symm = order := by
    haveI : Std.Antisymm fun a b : Fin 4 => p b < p a :=
      ⟨fun a b hab hba => absurd (hab.trans hba) (lt_irrefl _)⟩
    exact List.Perm.eq_of_pairwise' (List.pairwise_map.2 hdesc) sorted
      ((hperm.map S.slotEquiv.symm).trans ((finRange_map_perm S.slotEquiv.symm).trans perm.symm))
  have hpoints' : tracked.highestFirst.mapM (fun index =>
      input.certified.localizedRerootCursorSpatialPoint? (S.frame.cursorAt index)) =
        some points := by
    rw [← hmapEq, mapM_map_option] at hpoints
    rw [← hpoints]
    congr 1
    funext index
    exact S.spatialPoint_cursorAt index
  unfold localizedOccurrenceRule45DescriptorOrdered? localizedOccurrenceRule45SpatialEvidenceOrdered?
  rw [hcenter]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [S.frameComputed]
  simp only [Option.bind_some]
  rw [hsafe]
  simp only [Option.bind_some]
  rw [hpoints']
  simp only [Option.bind_some, hraw, hzero]
  simp [classifyTetrahedralRSPseudo]

end ActualCentrePhysicalSetup

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_eq_orderedDescriptor
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedRootComparison_of_independent_ne
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_eq_chiral
