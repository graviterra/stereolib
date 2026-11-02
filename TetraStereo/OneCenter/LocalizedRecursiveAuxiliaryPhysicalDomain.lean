import TetraStereo.OneCenter.LocalizedRetainedCutDescriptorTransport
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Physical domain and outcome algebra for recursive auxiliary correctness

The accepted cyclic root theorem asks every non-root detected center to be a physical terminal
twin or a *constitutionally rigid* calibrated center. `RecursiveAuxiliaryPhysicalDomain` keeps the
twin case and the calibration (actual coordinates, nonzero volume, orientation equal to the
physical configuration sign) and drops rigidity. `ofGeneralRigid` shows the old domain implies it.

The algebra below is used by the recursive transport proof:

* `completeRootOutcome_unique`: the independent optional outcome is unique.
* `completeRootOutcome_congr_order`: the outcome depends on the keys only through their strict
  order and their prior-tie relation.
* `completeRootOutcome_parent_congr`: one slot may change its key, provided its constitutional
  component is unchanged and strictly separated from the other three. This is the form in which the
  parent cut of a non-root target enters.
* `retainedCompleteLigandRule5KeyAt_congr`: a retained key depends on the descriptor map only at
  the occurrences its real nodes read.
* `hybridMap` and `readsAgree_hybridMap`: a source map whose reflected reads agree with the image
  map at every read, by construction. It equals the actual map exactly at covariant units.
* `cuts_completeRootOutcome_transport`: the accepted four-cut physical transport with a separate
  outer root per slot.

No label, reference, order, strictness or reader correspondence is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain

open CertifiedLocalizedCIPInput DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedRetainedMirrorDescriptorCorrectness
open Certificate.CanonicalSphereKey (Key)
open scoped Classical

noncomputable section

universe u

/-! ## The physical domain -/

/-- Actual coordinates of the four ligands of a center in the molecule's own enumeration, with
nonzero oriented volume and orientation equal to the physical configuration sign. No rigidity,
frame, label or automorphism condition. -/
def ActualPhysicalCalibratedCoordinates (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (cfg : m.Configuration) (center : m.Center) : Prop :=
  ∃ pointAt : Fin 4 → CartesianPoint3,
    (∀ i, input.spatialPointAt? (m.ligandAtomAt center i) = some (pointAt i)) ∧
      CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 ∧
      rationalVolumeSign
          (CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
        m.configurationSign cfg center

/-- **The recursive auxiliary physical domain** at one root of the detected molecule: every other
detected center is a physical terminal twin or has calibrated actual coordinates. Constitutional
symmetry at non-root centers is allowed. -/
structure RecursiveAuxiliaryPhysicalDomain (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) : Prop where
  centerCase : ∀ center : input.detectedMultiCenterMolecule.Center, center ≠ root →
    ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center ∨
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg center

/-- The accepted general-rigid domain is a special case. -/
theorem RecursiveAuxiliaryPhysicalDomain.ofGeneralRigid {input : CertifiedLocalizedCIPInput}
    {cfg : input.detectedMultiCenterMolecule.Configuration}
    {root : input.detectedMultiCenterMolecule.Center}
    (domain : ActualGeneralRigidPhysicalDomain input input.detectedMultiCenterMolecule cfg root) :
    RecursiveAuxiliaryPhysicalDomain input cfg root :=
  ⟨fun center ne => (domain.centerCase center ne).imp id fun calibrated => calibrated.2⟩

/-! ## Outcome algebra -/

/-- The independent optional outcome on fixed keys and points is unique. -/
theorem completeRootOutcome_unique {keys : Fin 4 → CompleteLigandRule5Key}
    {points : Fin 4 → CartesianPoint3} {first second : Option LocalizedAuxiliaryLabel}
    (hfirst : CompleteRootOutcome keys points first)
    (hsecond : CompleteRootOutcome keys points second) : first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some descriptor =>
          simp only [CompleteRootOutcome] at hfirst hsecond
          exact (hfirst ⟨descriptor, hsecond⟩).elim
  | some descriptor =>
      cases second with
      | none =>
          simp only [CompleteRootOutcome] at hfirst hsecond
          exact (hsecond ⟨descriptor, hfirst⟩).elim
      | some other =>
          simp only [CompleteRootOutcome] at hfirst hsecond
          exact congrArg some (completeRootDescriptorJudgment_unique hfirst hsecond)

/-- The prior-pair count depends only on the prior-tie relation. -/
theorem completeRule5PairCount_congr {keys keys' : Fin 4 → CompleteLigandRule5Key}
    (prior_iff : ∀ a b, (ofLex (keys a)).1 = (ofLex (keys b)).1 ↔
      (ofLex (keys' a)).1 = (ofLex (keys' b)).1) :
    completeRule5PairCount keys = completeRule5PairCount keys' := by
  have hiff : ∀ a b, CompletePriorPair keys a b ↔ CompletePriorPair keys' a b := fun a b =>
    and_congr Iff.rfl (prior_iff a b)
  have hcong := sourceEnantiomorphicPairCount_congr_of_forall
    (CompletePriorPair keys) (CompletePriorPair keys') hiff
  simpa [completeRule5PairCount] using hcong

/-- One judgment transfers between keys with the same strict order and prior-tie relation. -/
theorem completeRootDescriptorJudgment_congr_order {keys keys' : Fin 4 → CompleteLigandRule5Key}
    (lt_iff : ∀ a b, keys a < keys b ↔ keys' a < keys' b)
    (prior_iff : ∀ a b, (ofLex (keys a)).1 = (ofLex (keys b)).1 ↔
      (ofLex (keys' a)).1 = (ofLex (keys' b)).1)
    {points : Fin 4 → CartesianPoint3} {descriptor : LocalizedAuxiliaryLabel}
    (judgment : CompleteRootDescriptorJudgment keys points descriptor) :
    CompleteRootDescriptorJudgment keys' points descriptor := by
  obtain ⟨order, raw, perm, sorted, geometry, classified⟩ := judgment
  refine ⟨order, raw, perm, sorted.imp fun h => (lt_iff _ _).1 h, geometry, ?_⟩
  rw [classified, completeRule5PairCount_congr prior_iff]

/-- **Order invariance.** The independent optional outcome depends on the keys only through their
strict order and their prior-tie relation. -/
theorem completeRootOutcome_congr_order {keys keys' : Fin 4 → CompleteLigandRule5Key}
    (lt_iff : ∀ a b, keys a < keys b ↔ keys' a < keys' b)
    (prior_iff : ∀ a b, (ofLex (keys a)).1 = (ofLex (keys b)).1 ↔
      (ofLex (keys' a)).1 = (ofLex (keys' b)).1)
    (points : Fin 4 → CartesianPoint3) (outcome : Option LocalizedAuxiliaryLabel) :
    CompleteRootOutcome keys points outcome ↔ CompleteRootOutcome keys' points outcome := by
  have lt_iff' : ∀ a b, keys' a < keys' b ↔ keys a < keys b := fun a b => (lt_iff a b).symm
  have prior_iff' : ∀ a b, (ofLex (keys' a)).1 = (ofLex (keys' b)).1 ↔
      (ofLex (keys a)).1 = (ofLex (keys b)).1 := fun a b => (prior_iff a b).symm
  cases outcome with
  | none =>
      simp only [CompleteRootOutcome]
      constructor
      · intro none ⟨descriptor, judgment⟩
        exact none ⟨descriptor, completeRootDescriptorJudgment_congr_order lt_iff' prior_iff'
          judgment⟩
      · intro none ⟨descriptor, judgment⟩
        exact none ⟨descriptor, completeRootDescriptorJudgment_congr_order lt_iff prior_iff
          judgment⟩
  | some descriptor =>
      simp only [CompleteRootOutcome]
      exact ⟨completeRootDescriptorJudgment_congr_order lt_iff prior_iff,
        completeRootDescriptorJudgment_congr_order lt_iff' prior_iff'⟩

/-- The constitutional (Rules 1a/1b/2) component of a complete retained key. -/
def constitutionalComponent (key : CompleteLigandRule5Key) : List (Key ℤ) :=
  (ofLex (ofLex (ofLex key).1).1).1

private theorem toLex_lt_iff_of_fst_ne {α β : Type*} [LT α] [LT β] {a b : α × β}
    (distinct : a.1 ≠ b.1) : toLex a < toLex b ↔ a.1 < b.1 := by
  rw [Prod.Lex.lt_iff]
  constructor
  · rintro (lower | ⟨same, _⟩)
    · exact lower
    · exact absurd same distinct
  · exact Or.inl

private theorem lex_lt_iff_of_fst_ne {α β : Type*} [LT α] [LT β] {x y : Lex (α × β)}
    (distinct : (ofLex x).1 ≠ (ofLex y).1) : x < y ↔ (ofLex x).1 < (ofLex y).1 := by
  have h := toLex_lt_iff_of_fst_ne (a := ofLex x) (b := ofLex y) distinct
  rwa [toLex_ofLex, toLex_ofLex] at h

/-- Distinct constitutional components decide the complete key order. -/
theorem lt_iff_constitutional_of_ne {x y : CompleteLigandRule5Key}
    (distinct : constitutionalComponent x ≠ constitutionalComponent y) :
    x < y ↔ constitutionalComponent x < constitutionalComponent y := by
  have constNe : (ofLex (ofLex (ofLex x).1).1).1 ≠ (ofLex (ofLex (ofLex y).1).1).1 := distinct
  have rankNe : (ofLex (ofLex x).1).1 ≠ (ofLex (ofLex y).1).1 := fun same =>
    constNe (by rw [same])
  have priorNe : (ofLex x).1 ≠ (ofLex y).1 := fun same =>
    rankNe (by rw [same])
  rw [lex_lt_iff_of_fst_ne priorNe, lex_lt_iff_of_fst_ne rankNe, lex_lt_iff_of_fst_ne constNe]
  rfl

/-- Distinct constitutional components give distinct prior keys. -/
theorem prior_ne_of_constitutional_ne {x y : CompleteLigandRule5Key}
    (distinct : constitutionalComponent x ≠ constitutionalComponent y) :
    (ofLex x).1 ≠ (ofLex y).1 := fun same =>
  distinct (by unfold constitutionalComponent; rw [same])

/-- **Parent-slot congruence.** Replacing the key of one slot keeps the outcome when its
constitutional component is unchanged and strictly separated from the other three slots. -/
theorem completeRootOutcome_parent_congr (keys keys' : Fin 4 → CompleteLigandRule5Key)
    (parent : Fin 4) (others : ∀ slot, slot ≠ parent → keys' slot = keys slot)
    (sameConstitution :
      constitutionalComponent (keys' parent) = constitutionalComponent (keys parent))
    (separated : ∀ slot, slot ≠ parent →
      constitutionalComponent (keys parent) ≠ constitutionalComponent (keys slot))
    (points : Fin 4 → CartesianPoint3) (outcome : Option LocalizedAuxiliaryLabel) :
    CompleteRootOutcome keys' points outcome ↔ CompleteRootOutcome keys points outcome := by
  have separated' : ∀ slot, slot ≠ parent →
      constitutionalComponent (keys' parent) ≠ constitutionalComponent (keys' slot) := by
    intro slot ne
    rw [sameConstitution, others slot ne]
    exact separated slot ne
  have lt_iff : ∀ a b, keys' a < keys' b ↔ keys a < keys b := by
    intro a b
    by_cases ha : a = parent
    · subst ha
      by_cases hb : b = a
      · subst hb
        simp
      · rw [lt_iff_constitutional_of_ne (separated' b hb), lt_iff_constitutional_of_ne
          (separated b hb), sameConstitution, others b hb]
    · by_cases hb : b = parent
      · subst hb
        have neL : constitutionalComponent (keys' a) ≠ constitutionalComponent (keys' b) :=
          fun h => separated' a ha h.symm
        have ne : constitutionalComponent (keys a) ≠ constitutionalComponent (keys b) :=
          fun h => separated a ha h.symm
        rw [lt_iff_constitutional_of_ne neL, lt_iff_constitutional_of_ne ne, sameConstitution,
          others a ha]
      · rw [others a ha, others b hb]
  have prior_iff : ∀ a b, (ofLex (keys' a)).1 = (ofLex (keys' b)).1 ↔
      (ofLex (keys a)).1 = (ofLex (keys b)).1 := by
    intro a b
    by_cases ha : a = parent
    · subst ha
      by_cases hb : b = a
      · subst hb
        simp
      · exact iff_of_false (prior_ne_of_constitutional_ne (separated' b hb))
          (prior_ne_of_constitutional_ne (separated b hb))
    · by_cases hb : b = parent
      · subst hb
        exact iff_of_false (fun h => prior_ne_of_constitutional_ne (separated' a ha) h.symm)
          (fun h => prior_ne_of_constitutional_ne (separated a ha) h.symm)
      · rw [others a ha, others b hb]
  exact completeRootOutcome_congr_order lt_iff prior_iff points outcome

/-! ## Retained keys depend on the map only at their reads -/

section Reads

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)

theorem mapDetected_one (unit : DetectedOccurrence molecule) :
    mapDetected molecule 1 unit = unit := by
  apply Subtype.ext
  obtain ⟨⟨root, path⟩, _⟩ := unit
  simp [mapDetected, mapOccurrence]

theorem mapNodeLabel_one (label : NodeLabel Atom) :
    mapNodeLabel ((1 : molecule.Aut) : Equiv.Perm Atom) label = label := by
  cases label
  simp [mapNodeLabel]

/-- The identity relabel of a rooted graph along the identity molecular automorphism. -/
def identityRelabel (graph : RootedDigraph Atom) :
    RootedDigraph.Relabel ((1 : molecule.Aut) : Equiv.Perm Atom) graph graph where
  toEquiv := Equiv.refl _
  map_root := rfl
  map_child := fun _ _ => Iff.rfl
  map_label := fun node => mapNodeLabel_one molecule (graph.label node)
  map_depth := fun _ => rfl

/-- Two descriptor maps agreeing at every read occurrence of a graph with unique parents give the
same retained complete key. -/
theorem retainedCompleteLigandRule5KeyAt_congr (graph : RootedDigraph Atom)
    (parentUnique : ∀ a b n, graph.child a n → graph.child b n → a = b)
    (first second : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (agree : ∀ node steps occ, (graph.label node).provenance = NodeProvenance.realAtom →
      ancestorAtoms graph node = some steps →
      contextOccurrence molecule unit steps = some occ → first occ = second occ)
    (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule first unit graph W D =
      retainedCompleteLigandRule5KeyAt molecule second unit graph W D := by
  have reads : ReadsAgree molecule 1 first second unit graph := by
    intro node steps occ real ancestors context
    rw [mapDetected_one]
    exact agree node steps occ real ancestors context
  have prior := retainedCompleteLigandPriorKeyAt_relabel molecule unit 1 parentUnique first second
    reads (identityRelabel molecule graph) W D
  have rule5 := retainedCompleteRule5ReadingsAt_relabel molecule unit 1 parentUnique first second
    reads (identityRelabel molecule graph) W D .senior
  rw [mapDetected_one] at prior rule5
  unfold retainedCompleteLigandRule5KeyAt
  rw [prior, rule5]

/-- Cut form of `retainedCompleteLigandRule5KeyAt_congr`. -/
theorem cut_retainedCompleteLigandRule5KeyAt_congr {root : Atom} (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (anchor : CutAnchor focus incoming)
    (first second : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (agree : ∀ node steps occ,
      ((cutRetainedArm molecule root focus incoming anchor).label node).provenance =
        NodeProvenance.realAtom →
      ancestorAtoms (cutRetainedArm molecule root focus incoming anchor) node = some steps →
      contextOccurrence molecule unit steps = some occ → first occ = second occ)
    (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule first unit
        (cutRetainedArm molecule root focus incoming anchor) W D =
      retainedCompleteLigandRule5KeyAt molecule second unit
        (cutRetainedArm molecule root focus incoming anchor) W D :=
  retainedCompleteLigandRule5KeyAt_congr molecule _
    (fun a b n ha hb => cut_parent_unique focus incoming anchor a b n ha hb) first second unit
    agree W D

/-- The constitutional component of a retained key does not depend on the descriptor map. -/
theorem constitutionalComponent_map_independent (graph : RootedDigraph Atom)
    (first second : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (W D : ℕ) :
    constitutionalComponent (retainedCompleteLigandRule5KeyAt molecule first unit graph W D) =
      constitutionalComponent (retainedCompleteLigandRule5KeyAt molecule second unit graph W D) :=
  rfl

/-! ## The hybrid source map -/

/-- The source map seen through the mirror flag. -/
abbrev mirroredMap (mirror : Bool) (map : DescriptorMap (DetectedOccurrence molecule)) :
    DescriptorMap (DetectedOccurrence molecule) :=
  if mirror then map.reflect else map

/-- A unit is covariant when the map at its automorphic image is the (reflected) map at the unit. -/
def Covariant (e : molecule.Aut) (mirror : Bool) (map : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) : Prop :=
  map (mapDetected molecule e unit) = mirroredMap molecule mirror map unit

/-- The actual map at covariant units and the pulled-back, unreflected image elsewhere. -/
def hybridMap (e : molecule.Aut) (mirror : Bool)
    (map : DescriptorMap (DetectedOccurrence molecule)) :
    DescriptorMap (DetectedOccurrence molecule) := fun unit =>
  if Covariant molecule e mirror map unit then map unit
  else mirroredMap molecule mirror (fun other => map (mapDetected molecule e other)) unit

theorem descriptor_reflect_reflect (descriptor : Descriptor) :
    descriptor.reflect.reflect = descriptor := by
  cases descriptor <;> rfl

theorem hybridMap_of_covariant (e : molecule.Aut) (mirror : Bool)
    (map : DescriptorMap (DetectedOccurrence molecule)) {unit : DetectedOccurrence molecule}
    (covariant : Covariant molecule e mirror map unit) :
    hybridMap molecule e mirror map unit = map unit :=
  if_pos covariant

/-- **The hybrid map reads as the image map at every read, by construction.** -/
theorem readsAgree_hybridMap (e : molecule.Aut) (mirror : Bool)
    (map : DescriptorMap (DetectedOccurrence molecule)) (unit : DetectedOccurrence molecule)
    (graph : RootedDigraph Atom) :
    ReadsAgree molecule e map (mirroredMap molecule mirror (hybridMap molecule e mirror map))
      unit graph := by
  intro node steps occ _real _ancestors _context
  by_cases covariant : Covariant molecule e mirror map occ
  · have hybrid : hybridMap molecule e mirror map occ = map occ := if_pos covariant
    have cov : map (mapDetected molecule e occ) = mirroredMap molecule mirror map occ := covariant
    rw [cov]
    cases mirror with
    | false => exact hybrid.symm
    | true =>
        show (map occ).map Descriptor.reflect =
          (hybridMap molecule e true map occ).map Descriptor.reflect
        rw [hybrid]
  · have hybrid : hybridMap molecule e mirror map occ =
        mirroredMap molecule mirror (fun other => map (mapDetected molecule e other)) occ :=
      if_neg covariant
    cases mirror with
    | false => exact hybrid.symm
    | true =>
        show map (mapDetected molecule e occ) =
          (hybridMap molecule e true map occ).map Descriptor.reflect
        rw [hybrid]
        show map (mapDetected molecule e occ) =
          ((map (mapDetected molecule e occ)).map Descriptor.reflect).map Descriptor.reflect
        cases map (mapDetected molecule e occ) <;> simp [descriptor_reflect_reflect]

/-! ## Labels and descriptors -/

theorem localizedAuxiliaryDescriptor_retainedPhysicalLetter (mirror : Bool)
    (label : LocalizedAuxiliaryLabel) :
    localizedAuxiliaryDescriptor (retainedPhysicalLetter mirror label) =
      (if mirror then Descriptor.reflect else id) (localizedAuxiliaryDescriptor label) := by
  cases mirror <;> rcases label with ⟨raw⟩ | ⟨raw⟩ <;> cases raw <;>
    rfl

/-! ## Four cuts with one outer root per slot -/

/-- The accepted four-cut physical transport, with the outer root allowed to vary by slot. -/
theorem cuts_completeRootOutcome_transport
    (e : molecule.Aut) (mirror : Bool) (slotPerm : Equiv.Perm (Fin 4))
    (sourceMap imageMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (root : Fin 4 → Atom)
    (focus : ∀ slot, Nodes molecule (root slot))
    (incoming : ∀ slot, Option (Nodes molecule (root slot)))
    (anchor : ∀ slot, CutAnchor (focus slot) (incoming slot))
    (reads : ∀ slot, ReadsAgree molecule e imageMap (mirroredMap molecule mirror sourceMap) unit
      (cutRetainedArm molecule (root slot) (focus slot) (incoming slot) (anchor slot)))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3) (W D : ℕ)
    (outcome : Option LocalizedAuxiliaryLabel)
    (sign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints)) :
    CompleteRootOutcome
        (fun slot => retainedCompleteLigandRule5KeyAt molecule imageMap
          (mapDetected molecule e unit)
          (cutRetainedArm molecule ((e : Equiv.Perm Atom) (root (slotPerm⁻¹ slot)))
            (imageNode e (focus (slotPerm⁻¹ slot)))
            ((incoming (slotPerm⁻¹ slot)).map (imageNode e))
            (cutAnchor_image e (focus (slotPerm⁻¹ slot)) (incoming (slotPerm⁻¹ slot))
              (anchor (slotPerm⁻¹ slot)))) W D)
        imagePoints (Option.map (retainedPhysicalLetter mirror) outcome) ↔
      CompleteRootOutcome
        (fun slot => retainedCompleteLigandRule5KeyAt molecule sourceMap unit
          (cutRetainedArm molecule (root slot) (focus slot) (incoming slot) (anchor slot)) W D)
        sourcePoints outcome := by
  let graphs : Fin 4 → RootedDigraph Atom :=
    fun slot => cutRetainedArm molecule (root slot) (focus slot) (incoming slot) (anchor slot)
  have keyEq : (fun slot => retainedCompleteLigandRule5KeyAt molecule imageMap
      (mapDetected molecule e unit)
      (cutRetainedArm molecule ((e : Equiv.Perm Atom) (root (slotPerm⁻¹ slot)))
        (imageNode e (focus (slotPerm⁻¹ slot)))
        ((incoming (slotPerm⁻¹ slot)).map (imageNode e))
        (cutAnchor_image e (focus (slotPerm⁻¹ slot)) (incoming (slotPerm⁻¹ slot))
          (anchor (slotPerm⁻¹ slot)))) W D) =
      retainedImageKey molecule sourceMap unit mirror graphs slotPerm W D := by
    funext slot
    exact cut_rule5Key molecule e (focus (slotPerm⁻¹ slot)) (incoming (slotPerm⁻¹ slot))
      (anchor (slotPerm⁻¹ slot)) imageMap (mirroredMap molecule mirror sourceMap) unit
      (reads (slotPerm⁻¹ slot)) W D
  rw [keyEq]
  exact completeRootOutcome_retainedPhysical molecule sourceMap unit mirror graphs slotPerm
    sourcePoints imagePoints W D outcome sign

end Reads

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.RecursiveAuxiliaryPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.RecursiveAuxiliaryPhysicalDomain.ofGeneralRigid
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.completeRootOutcome_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.completeRule5PairCount_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.completeRootOutcome_congr_order
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.lt_iff_constitutional_of_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.completeRootOutcome_parent_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.retainedCompleteLigandRule5KeyAt_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.cut_retainedCompleteLigandRule5KeyAt_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.readsAgree_hybridMap
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.localizedAuxiliaryDescriptor_retainedPhysicalLetter
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain.cuts_completeRootOutcome_transport
