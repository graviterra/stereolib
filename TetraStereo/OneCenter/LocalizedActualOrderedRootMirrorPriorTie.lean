import TetraStereo.OneCenter.LocalizedActualOrderedRootPhysicalDataCore
import TetraStereo.OneCenter.LocalizedCumulativeMirrorPopulationTransport
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeyTransport
import TetraStereo.OneCenter.LocalizedPhysicalPseudoEndToEnd
import TetraStereo.KernelOnly

set_option autoImplicit false









































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry
open AcyclicCutBranchAutomorphism

namespace CertifiedLocalizedCIPInput

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## Table-wise congruence of the ordered reading lists -/

/-- Equal descriptor tables of two Rule-4b/4c readings. -/
abbrev ReadingTablesEq (left right : input.LocalizedRerootRule4bcReading) : Prop :=
  left.rule4bKey.descriptor = right.rule4bKey.descriptor ∧
    left.rule4cKey.descriptor = right.rule4cKey.descriptor

section Generic

variable (input)

private theorem sparseLayers_transCmp :
    Std.TransCmp (OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority) := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedCumulativeRule45Priority OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
  infer_instance

theorem compareByRule4b_eq_of_tablesEq {a b : input.LocalizedRerootRule4bcReading}
    (h : ReadingTablesEq a b) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b a b = .eq := by
  letI := sparseLayers_transCmp
  simp only [compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, h.1]
  exact Std.ReflCmp.compare_self

theorem compare4cDescriptor_eq_of_tablesEq {a b : input.LocalizedRerootRule4bcReading}
    (h : ReadingTablesEq a b) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      a.rule4cKey.descriptor b.rule4cKey.descriptor = .eq := by
  letI := sparseLayers_transCmp
  rw [h.2]
  exact Std.ReflCmp.compare_self

theorem compareRule4bcReadingsComplete_congr {a a' b b' : input.LocalizedRerootRule4bcReading}
    (ha : ReadingTablesEq a a') (hb : ReadingTablesEq b b') :
    input.compareRule4bcReadingsComplete a b = input.compareRule4bcReadingsComplete a' b' := by
  simp only [compareRule4bcReadingsComplete, compareLex,
    compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey, ha.1, ha.2, hb.1, hb.2]

/-- Pointwise equal tables tie under both reading-list comparators (lists of at most two). -/
theorem readingLists_tie_of_forall₂ {l l' : List input.LocalizedRerootRule4bcReading}
    (hlen : l.length ≤ 2) (h : List.Forall₂ ReadingTablesEq l l') :
    input.compareLocalizedRerootCompoundRule4bReadings l l' = .eq ∧
      input.compareLocalizedRerootCompoundRule4cReadings l l' = .eq := by
  match l, l', h, hlen with
  | [], [], .nil, _ => exact ⟨rfl, rfl⟩
  | [a], [a'], .cons ha .nil, _ =>
      constructor
      · simp [compareLocalizedRerootCompoundRule4bReadings, List.compareLex,
          input.compareByRule4b_eq_of_tablesEq ha]
      · simp [compareLocalizedRerootCompoundRule4cReadings, List.compareLex, Ordering.byKey,
          input.compare4cDescriptor_eq_of_tablesEq ha]
  | [a, b], [a', b'], .cons ha (.cons hb .nil), _ =>
      constructor
      · simp [compareLocalizedRerootCompoundRule4bReadings, List.compareLex,
          input.compareByRule4b_eq_of_tablesEq ha, input.compareByRule4b_eq_of_tablesEq hb]
      · simp [compareLocalizedRerootCompoundRule4cReadings, List.compareLex, Ordering.byKey,
          input.compare4cDescriptor_eq_of_tablesEq ha, input.compare4cDescriptor_eq_of_tablesEq hb]
  | _ :: _ :: _ :: _, _, _, hlen => exact absurd hlen (by simp)

/-- The outcome order is congruent under pointwise equal tables. -/
theorem rankReadings_tie_of_forall₂ {l l' : List input.LocalizedRerootRule4bcReading}
    (hlen : l.length ≤ 2) (h : List.Forall₂ ReadingTablesEq l l') :
    input.compareLocalizedRerootCompoundRule4bReadings
        (input.rankReadings l) (input.rankReadings l') = .eq ∧
      input.compareLocalizedRerootCompoundRule4cReadings
        (input.rankReadings l) (input.rankReadings l') = .eq := by
  match l, l', h, hlen with
  | [], [], .nil, _ => exact ⟨rfl, rfl⟩
  | [a], [a'], .cons ha .nil, _ =>
      have single : List.Forall₂ ReadingTablesEq [a] [a'] := .cons ha .nil
      exact input.readingLists_tie_of_forall₂ (l := [a]) (l' := [a']) (by simp) single
  | [a, b], [a', b'], .cons ha (.cons hb .nil), _ =>
      have congr := input.compareRule4bcReadingsComplete_congr ha hb
      have swapped : List.Forall₂ ReadingTablesEq [b, a] [b', a'] := .cons hb (.cons ha .nil)
      have straight : List.Forall₂ ReadingTablesEq [a, b] [a', b'] := .cons ha (.cons hb .nil)
      simp only [rankReadings, congr]
      split_ifs
      · exact input.readingLists_tie_of_forall₂ (by simp) swapped
      · exact input.readingLists_tie_of_forall₂ (by simp) straight
  | _ :: _ :: _ :: _, _, _, hlen => exact absurd hlen (by simp)

/-- **Ordered prior tie from reversed tables.**  Two compound Rules-4b/4c keys whose Rule-4a keys
tie, whose reference counts agree, and whose reading lists have pairwise equal tables after
reversing the left list, tie under the ordered prior comparator.  The reversal is absorbed by the
reflection invariance `outcomeOrdered_reflect_tie`. -/
theorem orderedPrior_tie_of_reverse_tables (keyL keyR : input.LocalizedRerootCompoundRule4bcKey)
    (hlen : keyL.readings.length ≤ 2)
    (h4a : input.compareLocalizedRerootCumulativeRule45Keys keyL.rule4aKey keyR.rule4aKey = .eq)
    (hcount : keyL.referenceCountPriority = keyR.referenceCountPriority)
    (htab : List.Forall₂ ReadingTablesEq keyL.readings.reverse keyR.readings) :
    input.compareLocalizedRerootCompoundRule4bcKeys (input.outcomeOrdered keyL)
      (input.outcomeOrdered keyR) = .eq := by
  letI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
    input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  refine Std.TransCmp.eq_trans (input.outcomeOrdered_reflect_tie keyL hlen) ?_
  rw [compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · have reflectTie : input.compareLocalizedRerootCumulativeRule45Keys
        (input.outcomeOrdered (compoundUppercaseCompoundRule4bcKey input keyL)).rule4aKey
          (input.outcomeOrdered keyR).rule4aKey =
        input.compareLocalizedRerootCumulativeRule45Keys keyL.rule4aKey keyR.rule4aKey := rfl
    rw [reflectTie]
    exact h4a
  · show compare keyL.referenceCountPriority keyR.referenceCountPriority = .eq
    simp [hcount]
  · have htab' : List.Forall₂ ReadingTablesEq
        ((keyL.readings.map (compoundUppercaseRule4bcReading input)).reverse) keyR.readings := by
      rw [← List.map_reverse]
      exact List.forall₂_map_left_iff.mpr (htab.imp fun a b hab => hab)
    exact input.rankReadings_tie_of_forall₂
      (by simpa [compoundUppercaseCompoundRule4bcKey] using hlen) htab'

/-! ## Builder plumbing -/

variable {input}
variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)
  (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)

/-- A successful reading list is built alternative by alternative. -/
theorem readings_forall₂_built :
    ∀ (alternatives : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor alternatives =
          some readings →
        List.Forall₂
          (fun alternative reading =>
            input.buildLocalizedRerootRule4bcReading? target view fuel cursor alternative =
              some reading)
          alternatives readings
  | [], readings, h => by
      simp only [buildLocalizedRerootRule4bcReadings?, Option.some.injEq] at h
      subst h
      exact List.Forall₂.nil
  | alternative :: alternatives, readings, h => by
      simp only [buildLocalizedRerootRule4bcReadings?] at h
      cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel cursor alternative with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
              alternatives with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
              subst h
              exact List.Forall₂.cons hr (readings_forall₂_built alternatives rest hrs)

/-- Both cumulative sub-builds of a successful no-reference reading. -/
theorem reading_none_built_full {r : input.LocalizedRerootRule4bcReading}
    (h : input.buildLocalizedRerootRule4bcReading? target view fuel cursor none = some r) :
    input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
        some r.rule4bKey ∧
      input.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference target view fuel cursor =
        some r.rule4cKey := by
  unfold buildLocalizedRerootRule4bcReading? at h
  cases h4b : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor with
  | none => simp [h4b] at h
  | some k4b =>
      cases h4c : input.buildLocalizedRerootCumulativeRule45Key? .rule4cNoReference target view
          fuel cursor with
      | none => simp [h4b, h4c] at h
      | some k4c =>
          simp [h4b, h4c] at h
          subst h
          exact ⟨rfl, rfl⟩

/-- Descriptor equality of two successful builds with transported observables. -/
theorem descriptor_eq_of_transported_builds {x y : input.LocalizedRerootCursor carrierFuel}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    (h : (input.buildLocalizedRerootCumulativeRule45Key? stageL target view fuel x).map
        input.localizedRerootCumulativeRule45Observable =
      (input.buildLocalizedRerootCumulativeRule45Key? stageR target view fuel y).map
        input.localizedRerootCumulativeRule45Observable)
    {kx ky : input.LocalizedRerootCumulativeRule45Key}
    (hx : input.buildLocalizedRerootCumulativeRule45Key? stageL target view fuel x = some kx)
    (hy : input.buildLocalizedRerootCumulativeRule45Key? stageR target view fuel y = some ky) :
    kx.descriptor = ky.descriptor := by
  rw [hx, hy] at h
  simp only [Option.map_some, Option.some.injEq] at h
  exact congrArg (fun observed => observed.descriptor) h

end Generic

/-- The three shapes of a P-92.5.2.1 selection. -/
theorem localizedRule4bReferencesFromPopulation_shape (descriptors : List RS) :
    localizedRule4bReferencesFromPopulation descriptors = [] ∨
      (∃ reference, localizedRule4bReferencesFromPopulation descriptors = [reference]) ∨
      localizedRule4bReferencesFromPopulation descriptors = [RS.R, RS.S] := by
  unfold localizedRule4bReferencesFromPopulation
  dsimp only
  split_ifs <;> simp

end CertifiedLocalizedCIPInput

/-! ## The physical centre setup -/

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The production evaluation fuel. -/
local notation "evalFuel" =>
  localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input)

/-- An automorphism fixing the centre and sending physical ligand `S.alpha i` to `S.alpha j`
relates the frame cursors of slots `i` and `j`. -/
theorem cursorCorrespondence_of_aut {i j : Fin 4}
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (centerFixed : input.certified.detectedMultiCenterMolecule.centerPerm e S.c = S.c)
    (ligandMaps : input.certified.detectedMultiCenterMolecule.ligandPermAt e S.c (S.alpha i) =
      S.alpha j) :
    LocalizedAutCursorCorrespondence input.certified
      (graphAutOfMultiCenterAut input.certified input.certified.detectedMultiCenterMolecule
        S.physicalDomain.graphEq e) S.c.1
      (S.frame.cursorAt i) (S.frame.cursorAt j) := by
  obtain ⟨frame', alpha', frameComputed', slotSpec', corr⟩ :=
    exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence input S.singleBonded
      S.acyclic input.certified.detectedMultiCenterMolecule S.physicalDomain.graphEq S.c e
      (S.alpha i) (S.alpha j) centerFixed ligandMaps
  have frameEq : frame' = S.frame :=
    Option.some.inj (frameComputed'.symm.trans S.frameComputed)
  subst frameEq
  have alphaEq : alpha' = S.alpha :=
    Equiv.ext fun index =>
      input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective S.c
        (Option.some.inj ((slotSpec' index).symm.trans (S.slotSpec index)))
  subst alphaEq
  simpa only [Equiv.symm_apply_apply] using corr

/-- **Mirror transport data at two frame slots.**  A physical mirror transport from ligand
`S.alpha i` to ligand `S.alpha j` gives the stage-wise observable transport of the production
builds at slots `i` and `j` (reflected stage on the right) and the selector covariance of the two
Rule-4a keys. -/
theorem mirror_data {i j : Fin 4}
    (mirror : MirrorTransport input.certified.detectedMultiCenterMolecule S.cfg S.c
      (S.alpha i) (S.alpha j)) :
    (∀ stage : LocalizedCumulativeRule45Stage,
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage S.top S.referenceView
          evalFuel (S.frame.cursorAt i)).map
          input.certified.localizedRerootCumulativeRule45Observable =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage) S.top S.referenceView evalFuel
          (S.frame.cursorAt j)).map
          input.certified.localizedRerootCumulativeRule45Observable) ∧
    localizedRule4bReferencesFromRankedLabels (S.frameKey j).prior.rule4aKey.rankedLabels =
      reflectSelectedRule4bReferences
        (localizedRule4bReferencesFromRankedLabels
          (S.frameKey i).prior.rule4aKey.rankedLabels) := by
  obtain ⟨e, centerFixed, ligandMaps, signLaw⟩ := mirror
  have corr := S.cursorCorrespondence_of_aut e centerFixed ligandMaps
  have relatedStart : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified input.certified.detectedMultiCenterMolecule
        S.physicalDomain.graphEq e) S.c.1
      (S.frame.cursorAt i) (S.frame.cursorAt j) (S.frame.cursorAt i) (S.frame.cursorAt j) :=
    ⟨corr, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  have obsThm :=
    localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
      input S.singleBonded S.acyclic S.hcharge S.noDouble S.cfg S.c e (S.alpha i) (S.alpha j)
      centerFixed (fun d h => by simpa using signLaw d h) S.physicalDomain S.frame S.alpha
      S.frameComputed S.slotSpec
  have readerThm :=
    localizedGeneralRigidPhysicalBranchRelation_reader_relation_globalDomain
      input S.singleBonded S.acyclic S.hcharge S.noDouble S.cfg S.c e true (S.alpha i) (S.alpha j)
      centerFixed (fun d h => by simpa using signLaw d h) S.physicalDomain S.frame S.alpha
      S.frameComputed S.slotSpec
  simp only [Equiv.symm_apply_apply] at obsThm readerThm
  have transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage S.top S.referenceView
          evalFuel (S.frame.cursorAt i)).map
          input.certified.localizedRerootCumulativeRule45Observable =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage) S.top S.referenceView evalFuel
          (S.frame.cursorAt j)).map
          input.certified.localizedRerootCumulativeRule45Observable :=
    fun stage => obsThm stage evalFuel _ _ relatedStart
  refine ⟨transported, ?_⟩
  have rootFixed : ((graphAutOfMultiCenterAut input.certified
      input.certified.detectedMultiCenterMolecule S.physicalDomain.graphEq e :
        input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) S.c.1 = S.c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) S.c.1 = S.c.1 :=
      (centerPerm_eq_iff input.certified.detectedMultiCenterMolecule e S.c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  exact input.certified.references_reflect_of_mirror_related S.top S.referenceView
    (LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified input.certified.detectedMultiCenterMolecule
        S.physicalDomain.graphEq e) S.c.1 (S.frame.cursorAt i) (S.frame.cursorAt j))
    (fun _ _ related =>
      localizedPhysicalBranchRelation_atomLabel input.certified S.singleBonded S.acyclic related)
    (fun _ _ related =>
      localizedPhysicalBranchRelation_rootDistance input.certified S.singleBonded S.acyclic
        rootFixed related)
    (fun _ _ related =>
      localizedPhysicalBranchRelation_children input.certified S.singleBonded S.acyclic
        (globalCarrierFuel_adequate input) related)
    (fun x y related => by
      have h := readerThm x y related
      simpa using h)
    evalFuel relatedStart (S.rule4aKey_built i) (S.rule4aKey_built j)

/-- Readings built at an alternative and at its swapped alternative on a mirror pair of slots have
equal tables. -/
theorem tablesEq_of_mirror_readings {i j : Fin 4}
    (transported : ∀ stage : LocalizedCumulativeRule45Stage,
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage S.top S.referenceView
          evalFuel (S.frame.cursorAt i)).map
          input.certified.localizedRerootCumulativeRule45Observable =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage) S.top S.referenceView evalFuel
          (S.frame.cursorAt j)).map
          input.certified.localizedRerootCumulativeRule45Observable)
    (alternative : Option RS) {a b : input.certified.LocalizedRerootRule4bcReading}
    (ha : input.certified.buildLocalizedRerootRule4bcReading? S.top S.referenceView evalFuel
      (S.frame.cursorAt i) alternative = some a)
    (hb : input.certified.buildLocalizedRerootRule4bcReading? S.top S.referenceView evalFuel
      (S.frame.cursorAt j) (alternative.map RS.swap) = some b) :
    ReadingTablesEq a b := by
  cases alternative with
  | none =>
      obtain ⟨a4b, a4c⟩ := reading_none_built_full _ _ _ _ ha
      obtain ⟨b4b, b4c⟩ := reading_none_built_full _ _ _ _ hb
      exact ⟨descriptor_eq_of_transported_builds _ _ _ (transported .rule4a) a4b b4b,
        descriptor_eq_of_transported_builds _ _ _ (transported .rule4cNoReference) a4c b4c⟩
  | some ρ =>
      obtain ⟨a4b, a4c, _⟩ := reading_some_built _ _ _ _ ρ ha
      obtain ⟨b4b, b4c, _⟩ := reading_some_built _ _ _ _ (RS.swap ρ) hb
      exact ⟨descriptor_eq_of_transported_builds _ _ _ (transported (.rule4b ρ)) a4b b4b,
        descriptor_eq_of_transported_builds _ _ _ (transported (.rule4c ρ)) a4c b4c⟩

/-- **The reverse bridge.**  A physical mirror transport between the ligands of two frame slots
gives an ordered prior tie of the slots. -/
theorem orderedPriorTie_of_mirrorTransport {i j : Fin 4}
    (mirror : MirrorTransport input.certified.detectedMultiCenterMolecule S.cfg S.c
      (S.alpha i) (S.alpha j)) :
    priorKeyTie input.certified (orderedKeys input.certified S.frameKey) i j := by
  obtain ⟨transported, refsEq⟩ := S.mirror_data mirror
  have builtL := actualSlotPriorBuilt input S.c S.frame S.frameComputed i
  have builtR := actualSlotPriorBuilt input S.c S.frame S.frameComputed j
  obtain ⟨_, hrefsL₀, hcountL₀, hreadL₀⟩ := compound_built_components _ _ _ _ builtL
  obtain ⟨_, hrefsR₀, hcountR₀, hreadR₀⟩ := compound_built_components _ _ _ _ builtR
  -- Restate the components in the setup's forms.
  have hrefsL : (S.frameKey i).prior.references =
      localizedRule4bReferencesFromRankedLabels (S.frameKey i).prior.rule4aKey.rankedLabels :=
    hrefsL₀
  have hrefsR : (S.frameKey j).prior.references =
      localizedRule4bReferencesFromRankedLabels (S.frameKey j).prior.rule4aKey.rankedLabels :=
    hrefsR₀
  have hcountL : (S.frameKey i).prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority (S.frameKey i).prior.references := hcountL₀
  have hcountR : (S.frameKey j).prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority (S.frameKey j).prior.references := hcountR₀
  have hreadL : input.certified.buildLocalizedRerootRule4bcReadings? S.top S.referenceView
      evalFuel (S.frame.cursorAt i)
      (localizedRule4bcReferenceAlternatives (S.frameKey i).prior.references) =
        some (S.frameKey i).prior.readings := hreadL₀
  have hreadR : input.certified.buildLocalizedRerootRule4bcReadings? S.top S.referenceView
      evalFuel (S.frame.cursorAt j)
      (localizedRule4bcReferenceAlternatives (S.frameKey j).prior.references) =
        some (S.frameKey j).prior.readings := hreadR₀
  have hlen : (S.frameKey i).prior.readings.length ≤ 2 :=
    (input.certified.built_prior_shape S.top S.referenceView evalFuel _ _ builtL).1
  clear hrefsL₀ hrefsR₀ hcountL₀ hcountR₀ hreadL₀ hreadR₀ builtL builtR
  have refsEq' : (S.frameKey j).prior.references =
      reflectSelectedRule4bReferences (S.frameKey i).prior.references := by
    rw [hrefsR, hrefsL]
    exact refsEq
  have shape : (S.frameKey i).prior.references = [] ∨
      (∃ reference, (S.frameKey i).prior.references = [reference]) ∨
      (S.frameKey i).prior.references = [RS.R, RS.S] := by
    rw [hrefsL]
    exact localizedRule4bReferencesFromPopulation_shape _
  have h4a : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (S.frameKey i).prior.rule4aKey (S.frameKey j).prior.rule4aKey = .eq := by
    rw [compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq]
    have h := transported .rule4a
    have h4aR' : input.certified.buildLocalizedRerootCumulativeRule45Key?
        (reflectLocalizedCumulativeRule45Stage .rule4a) S.top S.referenceView evalFuel
        (S.frame.cursorAt j) = some (S.frameKey j).prior.rule4aKey := S.rule4aKey_built j
    rw [S.rule4aKey_built i, h4aR'] at h
    simpa using h
  have hcount : (S.frameKey i).prior.referenceCountPriority =
      (S.frameKey j).prior.referenceCountPriority := by
    rw [hcountL, hcountR, refsEq',
      constitutionalRule4bReferenceCountPriority_reflectSelected_shape _ shape]
  have altsR : localizedRule4bcReferenceAlternatives (S.frameKey j).prior.references =
      ((localizedRule4bcReferenceAlternatives (S.frameKey i).prior.references).map
        (Option.map RS.swap)).reverse := by
    rw [refsEq']
    exact localizedRule4bcReferenceAlternatives_reflectSelected_shape _ shape
  have fL := readings_forall₂_built _ _ _ _ _ _ hreadL
  have fR := readings_forall₂_built _ _ _ _ _ _ hreadR
  rw [altsR] at fR
  have fR' : List.Forall₂
      (fun (alternative : Option RS) (reading : input.certified.LocalizedRerootRule4bcReading) =>
        input.certified.buildLocalizedRerootRule4bcReading? S.top S.referenceView evalFuel
          (S.frame.cursorAt j) (alternative.map RS.swap) = some reading)
      (localizedRule4bcReferenceAlternatives (S.frameKey i).prior.references)
      (S.frameKey j).prior.readings.reverse := by
    rw [← List.reverse_reverse (S.frameKey j).prior.readings] at fR
    exact List.forall₂_map_left_iff.mp (List.forall₂_reverse_iff.mp fR)
  have htab : List.Forall₂ ReadingTablesEq (S.frameKey i).prior.readings
      (S.frameKey j).prior.readings.reverse :=
    (forall₂_comp_left fL fR').imp fun a b h => by
      obtain ⟨alternative, ha, hb⟩ := h
      exact S.tablesEq_of_mirror_readings transported alternative ha hb
  have htab' : List.Forall₂ ReadingTablesEq (S.frameKey i).prior.readings.reverse
      (S.frameKey j).prior.readings := by
    have h := List.forall₂_reverse_iff.mpr htab
    rwa [List.reverse_reverse] at h
  exact input.certified.orderedPrior_tie_of_reverse_tables _ _ hlen h4a hcount htab'

/-! ## The physical pair count -/

section Distinct

variable (distinct : ∀ i j : Fin 4, i ≠ j →
  ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
include distinct

/-- **Ordered prior ties are exactly the physical enantiomorphic pairs.** -/
theorem orderedPriorTie_iff_enantiomorphic (i j : Fin 4) :
    compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j ↔
      Enantiomorphic input.certified.detectedMultiCenterMolecule S.cfg S.c
        (S.alpha i) (S.alpha j) := by
  constructor
  · exact S.enantiomorphic_of_orderedPriorTie distinct
  · rintro ⟨hne, mirror, _⟩
    exact ⟨fun h => hne (congrArg S.alpha h), S.orderedPriorTie_of_mirrorTransport mirror⟩

/-- **The ordered pseudo count is the physical enantiomorphic pair count.** -/
theorem orderedPriorTieCount_eq_physical :
    sourceEnantiomorphicPairCount
        (compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey)) =
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule S.cfg S.c :=
  sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_physicalCount input.certified
    input.certified.detectedMultiCenterMolecule S.cfg S.c S.alpha
    (orderedKeys input.certified S.frameKey) (S.orderedPriorTie_iff_enantiomorphic distinct)

/-- **The ordered Rule-5 root theorem with the physical pair count.**  In the physical centre
setup, under pairwise proper-distinguishability and nondegenerate canonical root coordinates, the
ordered evaluator's fixed point at the final occurrence is the pseudo-aware classification of the
oriented-volume reading of the actual slot coordinates in the sorted order; it is lowercase exactly
when the independent physical enantiomorphic pair count is one; the ordered prior ties are exactly
the physical enantiomorphic pairs; and the sorted order is descending in the independent keys
wherever they differ. -/
theorem orderedReferenceState_top_eq_classify_physical
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (normalizedRS : RS)
      (pointsAt : Fin 4 → CartesianPoint3),
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
        some (classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
            S.cfg S.c)) ∧
      (∀ index : Fin 4,
        input.certified.localizedRerootCursorSpatialPoint? (S.frame.cursorAt index) =
          some (pointsAt index)) ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      SortedByRank (input.certified.compoundKeyRank (orderedKeys input.certified S.frameKey))
        tracked.highestFirst.reverse ∧
      RationalTetrahedralDescriptor (tracked.highestFirst.map pointsAt) normalizedRS ∧
      ((classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
            S.cfg S.c)).IsLowercase ↔
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
          S.cfg S.c = 1) ∧
      (∀ i j : Fin 4,
        compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j ↔
          Enantiomorphic input.certified.detectedMultiCenterMolecule S.cfg S.c
            (S.alpha i) (S.alpha j)) ∧
      (tracked.highestFirst.map S.slotEquiv.symm).Pairwise fun ℓ m =>
        S.independentKey ℓ ≠ S.independentKey m → S.independentKey m < S.independentKey ℓ := by
  obtain ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, sorted, rational, _, _⟩ :=
    S.orderedReferenceState_top_eq_classify distinct coordinates
  rw [S.orderedPriorTieCount_eq_physical distinct] at stateEq
  exact ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, sorted, rational,
    isLowercase_classify_iff _ _, S.orderedPriorTie_iff_enantiomorphic distinct,
    S.highestFirst_pairwise_independentKey distinct tracked sorted⟩

/-- **Descriptor existence and the lowercase criterion.**  The ordered fixed point at the final
occurrence is some descriptor, lowercase exactly when the independent physical enantiomorphic pair
count is one. -/
theorem exists_orderedReferenceState_descriptor_lowercase_iff_physicalCount
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
          some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
            S.cfg S.c = 1) := by
  obtain ⟨_, normalizedRS, _, stateEq, -, -, -, -, lowercase, -, -⟩ :=
    S.orderedReferenceState_top_eq_classify_physical distinct coordinates
  exact ⟨_, stateEq, lowercase⟩

end Distinct

end ActualCentrePhysicalSetup
end Rule4aTableBridge

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderedPrior_tie_of_reverse_tables
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.mirror_data
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedPriorTie_of_mirrorTransport
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedPriorTie_iff_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedPriorTieCount_eq_physical
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_eq_classify_physical
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.exists_orderedReferenceState_descriptor_lowercase_iff_physicalCount
