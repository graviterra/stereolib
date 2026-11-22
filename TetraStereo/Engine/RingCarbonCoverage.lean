import TetraStereo.Engine.RingConstitutionalCache
import TetraStereo.Engine.RingExchangeCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingCarbonCoverage
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority
open LocalizedChemicalRing (Input)
open LocalizedChemicalRing.ConstitutionalPartition (Pair)

/-- Evidence for a row in the all-carbon report. Equality of atom indices binds both kinds
of official center evidence to the particular raw carbon being reported. -/
inductive Row (i : Input) (depth root : Nat) where
  | earlier (proof : RecursiveSigned.CarbonVerdict i.molecule
      (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) depth root)
  | strict (c : i.certified.TetrahedralCenter) (atRoot : c.1.val = root) (hand : RS)
      (proof : (c,.assigned hand) ∈ LocalizedChemicalRing.ConstitutionalPartition.report i)
  | exchange (proof : RingSharedArmRefusal.OfficialCertificate i depth root)

def Row.label {i depth root} : Row i depth root → Option LocalizedAuxiliaryLabel
  | .earlier v => v.label
  | .strict _ _ hand _ => some (.chiral hand)
  | .exchange _ => none

def atCenter? (i : Input) (d : Nat) (c : i.certified.TetrahedralCenter) : Option (Row i d c.1.val) :=
  match h : LocalizedChemicalRing.ConstitutionalPartition.Cached.classify i c with
  | .assigned hand => some (.strict c rfl hand
      ((LocalizedChemicalRing.ConstitutionalPartition.report_exact i c _).mpr
        (h.symm.trans (LocalizedChemicalRing.ConstitutionalPartition.Cached.classify_exact i c))))
  | .needsStereo [_] => (RingSharedArmRefusal.discover? i d c.1.val).map .exchange
  | _ => none

/-- An existing evidence-carrying decision is retained. If missing, the evaluator tries
complete constitutional separation and then searches the unique tied pair for an exchange. -/
def carbon? (i : Input) (d root : Nat) : Option (Row i d root) :=
  if !(i.molecule.atoms[root]?).any (fun a => a.element == .C) then none else
  (RecursiveSigned.carbon? i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
    d root).map Row.earlier <|>
    i.certified.canonicalTetrahedralCenters.findSome? fun c =>
      if same : c.1.val = root then same ▸ atCenter? i d c else none

abbrev Report (i : Input) (depth : Nat) := List ((root : Nat) × Row i depth root)

def report? (i : Input) (depth : Nat) : Option (Report i depth) :=
  (RingCarbonReport.carbons i.molecule).mapM fun root => (carbon? i depth root).map (Sigma.mk root)

def labels {i depth} (r : Report i depth) := r.map fun row => (row.1,row.2.label)

theorem report_projection (i : Input) (depth : Nat) :
    (report? i depth).map labels = (RingCarbonReport.carbons i.molecule).mapM
      (fun root => (carbon? i depth root).map (fun row => (root,row.label))) := by
  unfold report?
  generalize RingCarbonReport.carbons i.molecule = roots
  induction roots with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons,List.mapM_cons]
    cases head : carbon? i depth a <;>
      cases tail : as.mapM (m := Option) (fun root => (carbon? i depth root).map (Sigma.mk root)) <;>
      simp [tail,labels] at ih ⊢ <;> simp [← ih]

private theorem per_carbon (i : Input) (d : Nat) (root : Nat) (member : root ∈ RingCarbonReport.carbons i.molecule) :
    (carbon? i d root).isSome = true ↔
      (RecursiveSigned.carbon? i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) d root).isSome = true ∨
      ∃ c : i.certified.TetrahedralCenter, c.1.val = root ∧ (atCenter? i d c).isSome = true := by
  let prior := RecursiveSigned.carbon? i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) d root
  change (carbon? i d root).isSome = true ↔ prior.isSome = true ∨ _
  simp only [carbon?,(RingCarbonReport.mem_carbons.mp member).2,Bool.not_true,Bool.false_eq_true,if_false]
  change ((prior.map Row.earlier) <|> _).isSome = true ↔ _
  cases h : prior with
  | some v => simp
  | none =>
    change (i.certified.canonicalTetrahedralCenters.findSome? (fun c => if same : c.1.val = root then same ▸ atCenter? i d c else none)).isSome = true ↔ false = true ∨ _
    rw [List.findSome?_isSome_iff]
    simp only [Bool.false_eq_true,false_or]
    constructor
    · rintro ⟨c,_,got⟩
      split at got
      · rename_i eqRoot
        subst root
        exact ⟨c,rfl,got⟩
      · contradiction
    · rintro ⟨c,rfl,got⟩
      exact ⟨c,(i.certified.mem_canonicalTetrahedralCenters_iff c).mpr c.2,by simpa using got⟩

/-- Every previously covered carbon and every center with no constitutional ties is
automatically covered. A molecule may mix both kinds of carbon in the same report. -/
theorem report_of_prior_or_constitution (i : Input) (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (depth : Nat) (covered : ∀ root ∈ RingCarbonReport.carbons i.molecule,
      (RecursiveSigned.carbon? i.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) depth root).isSome = true ∨
      ∃ c : i.certified.TetrahedralCenter, c.1.val = root ∧
        LocalizedChemicalRing.ConstitutionalPartition.residual i c = []) :
    (report? i depth).isSome = true := by
  have go (roots : List Nat) (all : ∀ root ∈ roots, (carbon? i depth root).isSome = true) :
      (roots.mapM (m := Option) (fun root => (carbon? i depth root).map (Sigma.mk root))).isSome = true := by
    induction roots with
    | nil => rfl
    | cons r rs ih =>
      obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (all r (by simp))
      rw [List.mapM_cons]
      obtain ⟨vs,hs⟩ := Option.isSome_iff_exists.mp (ih (fun root mem => all root (by simp [mem])))
      simp [hv,hs]
  apply go
  intro root mem
  apply (per_carbon i depth root mem).mpr
  rcases covered root mem with old | ⟨c,eqRoot,empty⟩
  · exact Or.inl old
  · refine Or.inr ⟨c,eqRoot,?_⟩
    obtain ⟨hand,found⟩ := Option.isSome_iff_exists.mp ((RingStrictConstitution.assign?_isSome_iff i admitted c).mpr
      ((LocalizedChemicalRing.ConstitutionalPartition.strict_iff_empty i c).mpr empty))
    have assigned : LocalizedChemicalRing.ConstitutionalPartition.Cached.classify i c = .assigned hand := by
      rw [LocalizedChemicalRing.ConstitutionalPartition.Cached.classify_exact]
      simp only [LocalizedChemicalRing.ConstitutionalPartition.classify,empty,found]
    unfold atCenter?
    split
    · rfl
    · rename_i h; rw [assigned] at h; contradiction
    · exact False.elim (by grind)

/-- Optional finite reference evaluator. It tries the automatic report's per-carbon routes
first. At any remaining carbon it searches the entire shared-arm exchange class. -/
def exhaustiveReport? (i : Input) (depth : Nat) : Option (Report i depth) :=
  (RingCarbonReport.carbons i.molecule).mapM fun root =>
    ((carbon? i depth root <|> (RingSharedArmRefusal.completeExchange? i depth root).map Row.exchange)).map (Sigma.mk root)

/-- The finite reference report covers any mixture of known rows and structurally certified
shared-arm sites. The second disjunct quantifies over independent molecular evidence. -/
theorem exhaustive_report_iff (i : Input) (depth : Nat) :
    (exhaustiveReport? i depth).isSome = true ↔ ∀ root ∈ RingCarbonReport.carbons i.molecule,
      (carbon? i depth root).isSome = true ∨ Nonempty (RingSharedArmRefusal.OfficialCertificate i depth root) := by
  have all {α β : Type} (f : α → Option β) (xs : List α) :
      (xs.mapM f).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.mapM_cons,List.forall_mem_cons]
      cases h : f x <;> cases t : xs.mapM f <;> simp_all
  unfold exhaustiveReport?
  rw [all]
  apply forall_congr'
  intro root
  apply forall_congr'
  intro _
  rw [← RingSharedArmRefusal.complete_iff]
  cases carbon? i depth root <;> cases RingSharedArmRefusal.completeExchange? i depth root <;> simp

end TetraStereo.Engine.RingCarbonCoverage

assert_kernel_only TetraStereo.Engine.RingCarbonCoverage.atCenter?
assert_kernel_only TetraStereo.Engine.RingCarbonCoverage.report_projection

assert_kernel_only TetraStereo.Engine.RingCarbonCoverage.report_of_prior_or_constitution

assert_kernel_only TetraStereo.Engine.RingCarbonCoverage.exhaustive_report_iff
