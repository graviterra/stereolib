import TetraStereo.Engine.RingUniversalCompatibility
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate

set_option autoImplicit false

namespace TetraStereo.Engine.RingCalibratedCompatibility
open OneCenter CertifiedLocalizedCIPInput LocalizedChemicalRing CentresRing RingUniversalCompatibility
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission
open Examples.CentresRingSpiroCasing (molecule spatial renumbered moved originalLayouts renumberedLayouts)

private def rawVolume (g : SpatialConfiguration) (a b c d : Nat) : Option ℚ := do
  return CartesianPoint3.orientedVolume (← g.positions[a]?) (← g.positions[b]?) (← g.positions[c]?) (← g.positions[d]?)

private def volumes (mol : RawMolecule) (g : SpatialConfiguration) (i : Nat) : Bool :=
  let ns := mol.canonicalIncidentNeighbors i
  ns.all fun a => ns.all fun b => ns.all fun c => ns.all fun d =>
    !decide [a,b,c,d].Nodup || (rawVolume g a b c d).any (fun v => decide (v ≠ 0))

/-- Checking distinct permutations of actual neighbors gives the admission result
without evaluating the abstract implementation of canonical frame ordering. -/
private theorem coordinate_check (i : Input)
    (h : ∀ atom : i.certified.Atom, volumes i.molecule i.spatial atom.val = true) :
    coordinatesAdmitted i = true := by
  apply decide_eq_true
  intro center
  let mol := actualCanonicalMolecule i.certified
  let id (k : Fin 4) := (mol.ligandAtomAt center k).val
  have inside (k : Fin 4) : id k ∈ i.molecule.canonicalIncidentNeighbors center.val.val := by
    apply (i.molecule.mem_canonicalIncidentNeighbors_iff _ i.admissible.1.1 _).mpr
    exact (LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement i.admissible.1.1
      i.admissible.1.2 i.supported _ _).mp (mol.ligandAtomAt_adj center k)
  have inj : Function.Injective id := Fin.val_injective.comp (mol.ligandAtomAt_injective center)
  have distinct : [id 0,id 1,id 2,id 3].Nodup := by simp [List.nodup_cons,inj.eq_iff]
  have x := List.all_eq_true.mp (h center.val) _ (inside 0)
  have y := List.all_eq_true.mp x _ (inside 1)
  have z := List.all_eq_true.mp y _ (inside 2)
  have last := List.all_eq_true.mp z _ (inside 3)
  simp only [distinct,decide_true,Bool.not_true,Bool.false_or] at last
  obtain ⟨v,hv,nz⟩ := (Option.any_eq_true _ _).mp last
  apply (centerAdmitted_iff ..).mpr
  exact ⟨v,by simpa only [coordinateVolume?,spatialPointAt?,i.spatial_eq,rawVolume,id,mol] using hv,
    of_decide_eq_true nz⟩

set_option maxRecDepth 35000 in
set_option maxHeartbeats 3000000 in
private theorem checked_volumes :
    (∀ j : Fin 13, volumes molecule spatial j = true) ∧
    (∀ j : Fin 13, volumes renumbered moved j = true) ∧
    (∀ j : Fin 13, volumes molecule (MirrorCasing.reflectGeometry spatial) j = true) ∧
    (∀ j : Fin 13, volumes renumbered (MirrorCasing.reflectGeometry moved) j = true) := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem calibrated_presentations :
    coordinatesAdmitted originalSite.input = true ∧ coordinatesAdmitted renumberedSite.input = true ∧
    coordinatesAdmitted reflectedOriginalSite.input = true ∧ coordinatesAdmitted reflectedRenumberedSite.input = true :=
  ⟨coordinate_check _ checked_volumes.1,coordinate_check _ checked_volumes.2.1,
    coordinate_check _ checked_volumes.2.2.1,coordinate_check _ checked_volumes.2.2.2⟩

abbrev CalibratedInput := {i : Input // coordinatesAdmitted i = true}
abbrev CalibratedSite := {p : Site // coordinatesAdmitted p.input = true}

/-- The candidate need only be defined on the physically admitted public domain. -/
abbrev Candidate := CalibratedInput → Nat → Option Label

def result (a : Candidate) (p : CalibratedSite) := a ⟨p.val.input,p.property⟩ p.val.atom.val

def FaithfulOn (obs : Observed) (a : Candidate) : Prop :=
  ∀ (p : CalibratedSite) ls, obs p.val ls → sourceCode p.val ls = some (labelCode (result a p))

def RelabelsOn (a : Candidate) : Prop :=
  ∀ p q : CalibratedSite, Renumbers p.val q.val → result a p = result a q

def PreservesLowerSOn (a : Candidate) : Prop :=
  ∀ p q : CalibratedSite, Reflects p.val q.val → result a p = some (.pseudoasymmetric .s) →
    result a q = some (.pseudoasymmetric .s)

def MirrorsOn (a : Candidate) : Prop :=
  ∀ p q : CalibratedSite, Reflects p.val q.val → result a q = (result a p).map MirrorCasing.reflectLabel

private def orig : CalibratedSite := ⟨originalSite,calibrated_presentations.1⟩
private def rn : CalibratedSite := ⟨renumberedSite,calibrated_presentations.2.1⟩
private def mo : CalibratedSite := ⟨reflectedOriginalSite,calibrated_presentations.2.2.1⟩
private def mr : CalibratedSite := ⟨reflectedRenumberedSite,calibrated_presentations.2.2.2⟩

private theorem reindex : Renumbers orig.val rn.val := by
  refine ⟨Equiv.swap (0 : Fin 13) (3 : Fin 13),?_⟩
  decide +kernel

private theorem reflectO : Reflects orig.val mo.val := ⟨rfl,rfl,rfl⟩
private theorem reflectR : Reflects rn.val mr.val := ⟨rfl,rfl,rfl⟩

private theorem reported :
    sourceCode orig.val originalLayouts = some "S" ∧ sourceCode rn.val renumberedLayouts = some "s" ∧
    sourceCode mo.val originalLayouts = some "R" ∧ sourceCode mr.val renumberedLayouts = some "r" := by
  unfold sourceCode
  simp only [orig,rn,mo,mr,originalSite,renumberedSite,reflectedOriginalSite,reflectedRenumberedSite]
  rw [Examples.CentresRingSpiroCasing.original_report,Examples.CentresRingSpiroCasing.renumbered_report,
    show MirrorCasing.reflectGeometry spatial = Examples.CentresRingSpiroCasing.reflected spatial from rfl,
    show MirrorCasing.reflectGeometry moved = Examples.CentresRingSpiroCasing.reflected moved from rfl,
    Examples.CentresRingSpiroCasing.original_mirror_report,Examples.CentresRingSpiroCasing.renumbered_mirror_report]
  decide

/-- Even on the coordinate-admitted subtype, matching the recorded source is
incompatible separately with atom reindexing and with preservation of lowercase s.
The two contradictions each use just two physically admitted presentations. -/
theorem incompatible (obs : Observed) (seen : IncludesSpiro obs) :
    (¬ ∃ a, FaithfulOn obs a ∧ RelabelsOn a) ∧
    (¬ ∃ a, FaithfulOn obs a ∧ PreservesLowerSOn a) := by
  constructor
  · rintro ⟨a,fit,rel⟩
    have x := fit orig _ seen.1
    have y := fit rn _ seen.2.1
    rw [reported.1,rel orig rn reindex] at x
    rw [reported.2.1,← x] at y
    contradiction
  · rintro ⟨a,fit,fixed⟩
    have x := fit rn _ seen.2.1
    have y := fit mr _ seen.2.2.2
    rw [reported.2.1] at x
    have h : result a rn = some (.pseudoasymmetric .s) := by
      cases v : result a rn with
      | none => simp [v,labelCode] at x
      | some d => cases d with
        | chiral k | pseudoasymmetric k => cases k <;> simp_all [labelCode]
    rw [reported.2.2.2,fixed rn mr reflectR h] at y
    contradiction

private theorem includes : IncludesSpiro suiteObservation := by
  change _ ∈ [_,_,_,_] ∧ _ ∈ [_,_,_,_] ∧ _ ∈ [_,_,_,_] ∧ _ ∈ [_,_,_,_]
  simp

/-- The witness suite is concrete. Exact source agreement cannot coexist with either
reindexing or chemical mirror covariance even after every law is restricted to
coordinate-admitted inputs, with refusals admitted as candidate results. -/
theorem no_universal_calibrated_assignment :
    (¬ ∃ a, FaithfulOn suiteObservation a ∧ RelabelsOn a) ∧
    (¬ ∃ a, FaithfulOn suiteObservation a ∧ MirrorsOn a) := by
  refine ⟨(incompatible _ includes).1,?_⟩
  rintro ⟨a,fit,mirror⟩
  apply (incompatible _ includes).2
  refine ⟨a,fit,fun p q he hand => ?_⟩
  rw [mirror p q he,hand]
  rfl

private def suite : List (CalibratedSite × List Molecular.Layout) :=
  [(orig,originalLayouts),(rn,renumberedLayouts),(mo,originalLayouts),(mr,renumberedLayouts)]

def agreements (a : Candidate) := suite.countP fun (p,ls) => sourceCode p.val ls == some (labelCode (result a p))

theorem sharp_bound (a : Candidate) (rel : RelabelsOn a) (mir : MirrorsOn a) :
    agreements a ≤ 2 ∧ (agreements a = 2 ↔ result a ⟨originalSite,calibrated_presentations.1⟩ = some (.chiral .S)) := by
  change agreements a ≤ 2 ∧ (agreements a = 2 ↔ result a orig = some (.chiral .S))
  have e1 := (rel orig rn reindex).symm
  have e2 := mir orig mo reflectO
  have e3 := (mir rn mr reflectR).trans (congrArg (Option.map MirrorCasing.reflectLabel) e1)
  cases h : result a orig with
  | none => simp [agreements,suite,reported.1,reported.2.1,reported.2.2.1,reported.2.2.2,e1,e2,e3,h,labelCode]
  | some d => cases d with
    | chiral k | pseudoasymmetric k =>
      cases k <;> simp [agreements,suite,reported.1,reported.2.1,reported.2.2.1,reported.2.2.2,e1,e2,e3,h,
        labelCode,MirrorCasing.reflectLabel,RS.swap]

end TetraStereo.Engine.RingCalibratedCompatibility

assert_kernel_only TetraStereo.Engine.RingCalibratedCompatibility.calibrated_presentations
assert_kernel_only TetraStereo.Engine.RingCalibratedCompatibility.incompatible
assert_kernel_only TetraStereo.Engine.RingCalibratedCompatibility.no_universal_calibrated_assignment
assert_kernel_only TetraStereo.Engine.RingCalibratedCompatibility.sharp_bound
