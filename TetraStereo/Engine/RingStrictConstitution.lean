import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate
import TetraStereo.Engine.RingFrameCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingStrictConstitution
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation RingChemicalPriority
open LocalizedChemicalRingPhysicalSense (inputGeometry inputGeometry_val)

abbrev Context := Fin 4 → CIPRuleEngine.OfficialLigandRuleContext

/-- Every branch key is complete at the proved atom-count bound, including on cyclic graphs. -/
def key (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (k : Fin 4) : ExactOfficialRuleMajorKey i.Atom :=
  (i.buildExecutableExactOfficialRuleMajorKey (i.certified.input.molecule.atomCount+1)
    (.rootFromEdge c.val (i.canonicalLigandAtom c k))).get
      (by obtain ⟨_,found,_⟩ := i.buildExecutableExactOfficialRuleMajorKey_complete_default c k; rw [found]; rfl)

def constitution (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (a b : Fin 4) : Ordering :=
  cipTraceOutcome (ExactOfficialRuleMajorKey.compareTraceObserved i.moleculeGraph
    i.certified.input.molecule.semanticExactOfficialRule1aObservation (key i c a) (key i c b))

private theorem constitution_eq (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (a b : Fin 4) :
    constitution i c a b = ExactOfficialRuleMajorKey.compare i.moleculeGraph (key i c a) (key i c b) := by
  unfold constitution
  rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct,
    ExactOfficialRuleMajorKey.compareTrace_outcome]

private theorem key_found (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (a : Fin 4) :
    i.buildExecutableExactOfficialRuleMajorKey (i.certified.input.molecule.atomCount+1)
      (.rootFromEdge c.val (i.canonicalLigandAtom c a)) = some (key i c a) := (Option.some_get _).symm

private theorem key_complete (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (a : Fin 4) :
    (key i c a).complete = true := by
  obtain ⟨k,found,complete⟩ := i.buildExecutableExactOfficialRuleMajorKey_complete_default c a
  obtain rfl := Option.some.inj (found.symm.trans (key_found i c a))
  exact complete

theorem constitutional_outcome (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (a b : Fin 4) :
    (i.compareRuleMajorConstitutionAt? c a b).map CIPTraceCertificate.outcome = some (constitution i c a b) := by
  obtain ⟨o,ok⟩ := Option.isSome_iff_exists.mp (ExactOfficialRuleMajorKey.compare?_isSome_of_complete
    i.moleculeGraph (key i c a) (key i c b) (key_complete i c a) (key_complete i c b))
  have safe : ExactOfficialRuleMajorKey.compareObserved? i.moleculeGraph
      i.certified.input.molecule.semanticExactOfficialRule1aObservation (key i c a) (key i c b) = some o := by
    rw [ExactOfficialRuleMajorKey.compareObserved?_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct]
    exact ok
  simp [compareRuleMajorConstitutionAt?,key_found,safe,constitution]

/-- Chemical separability through complete Rules 1a, 1b and 2. -/
def Strict (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) : Prop :=
  ∀ a b : Fin 4, a ≠ b → constitution i c a b ≠ .eq

instance {i c} : Decidable (Strict i c) := by unfold Strict; infer_instance

/-- Each strictly constitutional decision retains its complete trace under
every possible later context. -/
theorem strict_trace {i : CertifiedLocalizedCIPInput} {c : i.TetrahedralCenter} {a b : Fin 4}
    (strict : constitution i c a b ≠ .eq) (ctx : Context) :
    i.compareRuleMajorAt? c ctx a b = i.compareRuleMajorConstitutionAt? c a b := by
  obtain ⟨cert,found⟩ := Option.isSome_iff_exists.mp (i.compareRuleMajorConstitutionAt?_isSome c a b)
  have value : cert.outcome = constitution i c a b := by simpa [found] using constitutional_outcome i c a b
  have ne : cipTraceOutcome cert.trace ≠ .eq := by rwa [cert.sound,value]
  rw [compareRuleMajorAt?,found]
  change some (CIPTraceCertificate.ofTrace (CIPRuleEngine.compareDigraphThenOfficialTrace cert.trace _ _)) = some cert
  rw [CIPRuleEngine.compareDigraphThenOfficialTrace,if_neg ne]
  cases cert with
  | mk trace outcome sound => cases sound; rfl

private theorem outcomes {i : CertifiedLocalizedCIPInput} {c : i.TetrahedralCenter} (s : Strict i c)
    (ctx : Context) (a b : Fin 4) :
    (i.compareRuleMajorAt? c ctx a b).map CIPTraceCertificate.outcome = some (constitution i c a b) := by
  by_cases same : a = b
  · subst b
    letI := ExactOfficialRuleMajorKey.compare_transCmp i.moleculeGraph
    rw [i.compareRuleMajorAt?_outcome_self,constitution_eq]
    exact congrArg some (Std.ReflCmp.compare_self (cmp := ExactOfficialRuleMajorKey.compare i.moleculeGraph)
      (a := key i c a)).symm
  · rw [strict_trace (s _ _ same)]
    exact constitutional_outcome i c a b

def order (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) : List (Fin 4) :=
  (List.finRange 4).mergeSort fun a b => (constitution i c a b).isGE

theorem order_perm (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) : (order i c).Perm (List.finRange 4) :=
  List.mergeSort_perm ..

private theorem order_strict {i : CertifiedLocalizedCIPInput} {c : i.TetrahedralCenter} (s : Strict i c) :
    (order i c).Pairwise (fun a b => constitution i c a b = .gt) := by
  let cmp := ExactOfficialRuleMajorKey.compare i.moleculeGraph
  letI : Std.TransCmp cmp := ExactOfficialRuleMajorKey.compare_transCmp _
  have le (a b d : Fin 4) : (constitution i c a b).isGE → (constitution i c b d).isGE → (constitution i c a d).isGE := by
    simp only [constitution_eq]
    exact Std.TransCmp.isGE_trans (cmp := cmp)
  have total (a b : Fin 4) : ((constitution i c a b).isGE || (constitution i c b a).isGE) = true := by
    simp only [constitution_eq]
    change ((cmp _ _).isGE || (cmp _ _).isGE) = true
    rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := key i c a) (b := key i c b)]
    cases cmp (key i c b) (key i c a) <;> rfl
  have sorted := List.pairwise_mergeSort le total (List.finRange 4)
  have distinct := (order_perm i c).nodup_iff.mpr (List.nodup_finRange 4)
  apply (List.pairwise_and_iff.mpr ⟨sorted,distinct⟩).imp
  intro a b h
  have ne := s a b h.2
  cases v : constitution i c a b <;> simp_all

/-- Arbitrary later contexts, including separate contexts on the mirror
geometry, produce exactly this same order in the actual checked sorter. -/
theorem checked_order {i : CertifiedLocalizedCIPInput} {c : i.TetrahedralCenter} (s : Strict i c) (ctx : Context) :
    i.ruleMajorLigandOrderAt? c ctx = some (order i c) := by
  have before (a b : Fin 4) : i.ruleMajorLigandBeforeAt c ctx a b = (constitution i c a b).isGE := by
    obtain ⟨cert,found⟩ := Option.isSome_iff_exists.mp (i.compareRuleMajorAt?_isSome c ctx a b)
    have eqn : cert.outcome = constitution i c a b := by simpa [found] using outcomes s ctx a b
    simp only [ruleMajorLigandBeforeAt,found,eqn]
    cases v : constitution i c a b with
    | lt | gt => rfl
    | eq =>
      have same : a = b := by by_contra ne; exact s a b ne v
      simp [same]
  have same : i.ruleMajorLigandOrderAt c ctx = order i c := by
    unfold ruleMajorLigandOrderAt order
    rw [show i.ruleMajorLigandBeforeAt c ctx = _ from funext fun a => funext (before a)]
  apply (i.ruleMajorLigandOrderAt?_eq_some_iff ..).mpr
  refine ⟨?_,?_,same⟩
  · apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro b _
    by_cases ab : a = b
    · simp [ab]
    · obtain ⟨cert,h⟩ := Option.isSome_iff_exists.mp (i.compareRuleMajorAt?_isSome c ctx a b)
      have eqn : cert.outcome = constitution i c a b := by simpa [h] using outcomes s ctx a b
      simp [ab,ruleMajorPairResolvedAt?,h,eqn,s a b ab]
  · unfold ruleMajorOrderCoherentAt?
    rw [same,i.ruleMajorOrderCoherentListAt?_eq_true_iff]
    apply (order_strict s).imp
    intro a b gt
    exact Option.map_eq_some_iff.mp ((outcomes s ctx a b).trans (congrArg some gt))

def atomIds (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (slots : List (Fin 4)) :=
  slots.map fun k => (i.canonicalLigandAtom c k).val

/-- On the coordinate-admitted public model, each completely constitutional
center has a hand. Its mirror has the opposite hand in the same priority
order, so the character is uppercase. -/
theorem assigned (input : LocalizedChemicalRing.Input) (admitted : LocalizedChemicalRing.coordinatesAdmitted input = true)
    (c : input.certified.TetrahedralCenter) (strict : Strict input.certified c) :
    let i := input.certified
    let g := inputGeometry i
    let atoms := atomIds i c (order i c)
    ∃ hand, (∀ ctx, i.ruleMajorLigandOrderAt? c ctx = some (order i c) ∧
        i.DeclarativeRuleMajorPriorityOrder c ctx (order i c)) ∧
      readback? g atoms = some hand ∧ readback? (mirror g) atoms = some hand.swap ∧
      (Recursive.geometric g atoms atoms).bind Recursive.Reading.label = some (.chiral hand) := by
  let i := input.certified
  let atom := fun k : Fin 4 => (i.canonicalLigandAtom c k).val
  let g := inputGeometry i
  obtain ⟨pt,points,nonzero,_⟩ :=
    LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated input.certified admitted c
  have seen : (readback? g ([atom 0,atom 1,atom 2,atom 3])).isSome = true := by
    have observe (k : Fin 4) : g (atom k) = some (pt k) := (inputGeometry_val i _).trans (points k)
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · simp [readback?,observe,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
    · simp [readback?,observe,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]
  have nodup : ((List.finRange 4).map atom).Nodup :=
    List.Nodup.map (Fin.val_injective.comp (i.canonicalLigandAtom_injective c)) (List.nodup_finRange 4)
  have perm := (order_perm i c).map atom
  have canonical : ((List.finRange 4).map atom) = [atom 0,atom 1,atom 2,atom 3] := rfl
  rw [canonical] at nodup perm
  obtain ⟨hand,raw⟩ := Option.isSome_iff_exists.mp
    (ReferenceFrame.readback_all_permutations nodup rfl seen _ perm)
  refine ⟨hand,fun ctx => ⟨checked_order strict ctx,i.ruleMajorLigandOrderAt?_sound_declarative _ _ _ (checked_order strict ctx)⟩,raw,?_,?_⟩
  · change readback? (mirror g) (List.map atom (order i c)) = some hand.swap
    rw [readback_mirror,raw]
    rfl
  · change (Recursive.geometric g (List.map atom (order i c)) (List.map atom (order i c))).bind _ = _
    have observed : Recursive.geometric g (List.map atom (order i c)) (List.map atom (order i c)) = some ⟨hand,hand.swap⟩ := by
      simp [Recursive.geometric,readback_mirror,raw]
    rw [observed]
    exact (Recursive.constitutional_casing observed).2.2

/-- Read the coordinate hand only after the complete constitutional comparisons
separate all four canonical ligands. Outer absence leaves later rules open. -/
def assign? (input : LocalizedChemicalRing.Input) (c : input.certified.TetrahedralCenter) : Option RS :=
  let i := input.certified
  if Strict i c then readback? (inputGeometry i) (atomIds i c (order i c)) else none

theorem assign?_isSome_iff (input : LocalizedChemicalRing.Input)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted input = true) (c : input.certified.TetrahedralCenter) :
    (assign? input c).isSome = true ↔ Strict input.certified c := by
  by_cases s : Strict input.certified c
  · obtain ⟨h,_,raw,_,_⟩ := assigned input admitted c s
    simp [assign?,s,raw]
  · simp [assign?,s]

end TetraStereo.Engine.RingStrictConstitution

assert_kernel_only TetraStereo.Engine.RingStrictConstitution.constitutional_outcome
assert_kernel_only TetraStereo.Engine.RingStrictConstitution.strict_trace
assert_kernel_only TetraStereo.Engine.RingStrictConstitution.checked_order
assert_kernel_only TetraStereo.Engine.RingStrictConstitution.assigned
assert_kernel_only TetraStereo.Engine.RingStrictConstitution.assign?_isSome_iff
