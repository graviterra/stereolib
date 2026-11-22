import TetraStereo.Examples.CentresRingSpiroCasing

set_option autoImplicit false

namespace TetraStereo.Engine.RingUniversalCompatibility

open OneCenter CertifiedLocalizedCIPInput LocalizedChemicalRing CentresRing
open Examples.CentresRingSpiroCasing (molecule spatial renumbered moved originalLayouts renumberedLayouts)
abbrev Label := LocalizedAuxiliaryLabel

/-- A molecular presentation and a queried atom in the public structural admission domain. -/
structure Site where
  mol : RawMolecule
  xyz : SpatialConfiguration
  atom : Fin mol.atomCount
  admitted : (admitRawSpatial? mol xyz).isSome = true

def Site.input (p : Site) : Input := (admitRawSpatial? p.mol p.xyz).get p.admitted

/-- The candidate may return a descriptor, with its chemical case, or refuse. -/
abbrev Assignment := Input → Nat → Option Label

def atSite (a : Assignment) (p : Site) := a p.input p.atom.val

private def renameIndex {n k : Nat} (e : Fin n ≃ Fin k) (a : Nat) : Nat :=
  if valid : a < n then (e ⟨a,valid⟩).val else a

/-- One bijection carries the focused atom, complete atom specifications,
positions, ordered bond records with their kinds, optional written-neighbor
orders and token introduction predecessors. This also preserves any written
tetrahedral parity convention using those orders. -/
def Renumbers (p q : Site) : Prop := ∃ e : Fin p.mol.atomCount ≃ Fin q.mol.atomCount,
  e p.atom = q.atom ∧
    (∀ x, q.mol.atoms[(e x).val]? = p.mol.atoms[x.val]? ∧
      q.xyz.positions[(e x).val]? = p.xyz.positions[x.val]?) ∧
    q.mol.bonds = p.mol.bonds.map (fun bond =>
      {bond with source := renameIndex e bond.source,target := renameIndex e bond.target}) ∧
    (∀ x, q.mol.neighborOrder[(e x).val]? =
      p.mol.neighborOrder[x.val]?.map (List.map (renameIndex e)) ∧
      q.mol.introductionPredecessors[(e x).val]? =
      p.mol.introductionPredecessors[x.val]?.map (Option.map (renameIndex e))) ∧
    ∀ x y, q.mol.bondOrder (e x).val (e y).val = p.mol.bondOrder x.val y.val

def RelabelInvariant (a : Assignment) : Prop :=
  ∀ p q, Renumbers p q → atSite a p = atSite a q

def Reflects (p q : Site) : Prop :=
  q.mol = p.mol ∧ q.xyz = MirrorCasing.reflectGeometry p.xyz ∧ q.atom.val = p.atom.val

/-- Under reflection uppercase R/S exchange, lowercase r/s each stay fixed,
and a refusal stays a refusal. The independent relabeling theorem needs none
of these reflection requirements. -/
def MirrorCovariant (a : Assignment) : Prop :=
  ∀ p q, Reflects p q → atSite a q = (atSite a p).map MirrorCasing.reflectLabel

def originalSite : Site := ⟨molecule,spatial,⟨0,by decide⟩,Examples.CentresRingSpiroCasing.admitted.1⟩
def renumberedSite : Site := ⟨renumbered,moved,⟨3,by decide⟩,Examples.CentresRingSpiroCasing.admitted.2.2.1⟩
def reflectedOriginalSite : Site := ⟨molecule,MirrorCasing.reflectGeometry spatial,⟨0,by decide⟩,Examples.CentresRingSpiroCasing.admitted.2.1⟩
def reflectedRenumberedSite : Site := ⟨renumbered,MirrorCasing.reflectGeometry moved,⟨3,by decide⟩,Examples.CentresRingSpiroCasing.admitted.2.2.2⟩

private theorem renumbers_orig : Renumbers originalSite renumberedSite := by
  refine ⟨(Equiv.swap (0 : Fin 13) (3 : Fin 13)),?_⟩
  decide +kernel

private theorem mirrors_orig : Reflects originalSite reflectedOriginalSite := ⟨rfl,rfl,rfl⟩
private theorem mirrors_rn : Reflects renumberedSite reflectedRenumberedSite := ⟨rfl,rfl,rfl⟩

/-- An observation carries the layout used by the molecular reconstruction.
Its source status is external evidence. No assertion that arbitrary layouts are
real source executions or that their descriptor is chemically correct is needed. -/
abbrev Observed := Site → List Molecular.Layout → Prop

/-- Inclusion of the four layouts from the authenticated release comparison.
A larger domain may add other runs freely. -/
def IncludesSpiro (obs : Observed) : Prop :=
  obs originalSite originalLayouts ∧ obs renumberedSite renumberedLayouts ∧ obs reflectedOriginalSite originalLayouts ∧ obs reflectedRenumberedSite renumberedLayouts

/-- The source code at this atom is projected from the complete five-center
report in the witness. An absent report/atom differs from a recorded refusal. -/
def sourceCode (p : Site) (layouts : List Molecular.Layout) : Option String :=
  (Examples.CentresRingSpiroCasing.fullReport p.mol p.xyz layouts).bind (List.lookup p.atom.val)

def Faithful (obs : Observed) (a : Assignment) : Prop :=
  ∀ p ls, obs p ls → sourceCode p ls = some (labelCode (atSite a p))

private theorem codes :
    sourceCode originalSite originalLayouts = some "S" ∧ sourceCode renumberedSite renumberedLayouts = some "s" ∧
    sourceCode reflectedOriginalSite originalLayouts = some "R" ∧ sourceCode reflectedRenumberedSite renumberedLayouts = some "r" := by
  unfold sourceCode
  simp only [originalSite,renumberedSite,reflectedOriginalSite,reflectedRenumberedSite]
  rw [Examples.CentresRingSpiroCasing.original_report,Examples.CentresRingSpiroCasing.renumbered_report,
    show MirrorCasing.reflectGeometry spatial = Examples.CentresRingSpiroCasing.reflected spatial from rfl,
    show MirrorCasing.reflectGeometry moved = Examples.CentresRingSpiroCasing.reflected moved from rfl,
    Examples.CentresRingSpiroCasing.original_mirror_report,Examples.CentresRingSpiroCasing.renumbered_mirror_report]
  decide

/-- Every algorithm on the full public structural domain, including partial
descriptor assignments, fails at least one of exact source fidelity or invariance
under a pure change of atom indices. Two observed layouts suffice. -/
theorem no_relabel_and_fidelity (obs : Observed) (seen : obs originalSite originalLayouts ∧ obs renumberedSite renumberedLayouts) :
    ¬ ∃ a : Assignment, Faithful obs a ∧ RelabelInvariant a := by
  rintro ⟨a,fit,invariant⟩
  have first := fit _ _ seen.1
  have second := fit _ _ seen.2
  rw [codes.1,invariant _ _ renumbers_orig] at first
  rw [codes.2.1,← first] at second
  contradiction

/-- Exact source fidelity separately conflicts with the chemical mirror law,
even if one makes no atom-relabeling demand. The witness is the same numbered
molecule, with only its spatial configuration reflected. -/
theorem no_reflection_and_fidelity (obs : Observed) (seen : obs renumberedSite renumberedLayouts ∧ obs reflectedRenumberedSite renumberedLayouts) :
    ¬ ∃ a : Assignment, Faithful obs a ∧ MirrorCovariant a := by
  rintro ⟨a,fit,mirror⟩
  have first := fit _ _ seen.1
  have second := fit _ _ seen.2
  rw [codes.2.1] at first
  rw [codes.2.2.2,mirror _ _ mirrors_rn] at second
  cases h : atSite a renumberedSite with
  | none => simp [h,labelCode] at first
  | some d =>
    cases d with
    | chiral k => cases k <;> simp [h,labelCode] at first
    | pseudoasymmetric k => cases k <;> simp [h,labelCode,MirrorCasing.reflectLabel] at first second

/-- The closed obstruction transfers to any collection of observed runs that
includes the four authenticated presentations. -/
theorem universal_incompatibility (obs : Observed) (seen : IncludesSpiro obs) :
    (¬ ∃ a : Assignment, Faithful obs a ∧ RelabelInvariant a) ∧
    (¬ ∃ a : Assignment, Faithful obs a ∧ MirrorCovariant a) :=
  ⟨no_relabel_and_fidelity _ ⟨seen.1,seen.2.1⟩,no_reflection_and_fidelity _ ⟨seen.2.1,seen.2.2.2⟩⟩

private def sample : List (Site × List Molecular.Layout) :=
  [(originalSite,originalLayouts),(renumberedSite,renumberedLayouts),(reflectedOriginalSite,originalLayouts),(reflectedRenumberedSite,renumberedLayouts)]

/-- Number of exact agreements on the corresponding spiro atom in four full
reports, counting a refusal as an ordinary proposed response. -/
def agreements (a : Assignment) : Nat :=
  sample.countP fun (p,layouts) => sourceCode p layouts == some (labelCode (atSite a p))

/-- At most two of the four published results can be reproduced simultaneously.
The upper bound is reached only by predicting S under both numberings and R
under both reflected numberings. This is a bound on agreement with this
finite suite, without any claim of universal chemical truth of those predictions. -/
theorem sharp_spiro_bound (a : Assignment) (rel : RelabelInvariant a) (mir : MirrorCovariant a) :
    agreements a ≤ 2 ∧ (agreements a = 2 ↔ atSite a originalSite = some (.chiral .S)) := by
  have eq₁ := (rel _ _ renumbers_orig).symm
  have eq₂ := mir _ _ mirrors_orig
  have eq₃ := (mir _ _ mirrors_rn).trans (congrArg (Option.map MirrorCasing.reflectLabel) eq₁)
  cases h : atSite a originalSite with
  | none => simp [agreements,sample,codes.1,codes.2.1,codes.2.2.1,codes.2.2.2,eq₁,eq₂,eq₃,h,labelCode]
  | some d =>
    cases d with
    | chiral k | pseudoasymmetric k =>
      cases k <;> simp [agreements,sample,codes.1,codes.2.1,codes.2.2.1,codes.2.2.2,eq₁,eq₂,eq₃,h,labelCode,MirrorCasing.reflectLabel,RS.swap]

/-- The exact source outputs already conflict with preserving just lowercase s
on reflection. This proof imposes no behavior on R, S, r or a refusal. -/
theorem no_lower_s_and_fidelity (obs : Observed) (seen : obs renumberedSite renumberedLayouts ∧ obs reflectedRenumberedSite renumberedLayouts) :
    ¬ ∃ a : Assignment, Faithful obs a ∧
      (∀ p q, Reflects p q → atSite a p = some (.pseudoasymmetric .s) →
        atSite a q = some (.pseudoasymmetric .s)) := by
  rintro ⟨a,fit,fixed⟩
  have first := fit _ _ seen.1
  have last := fit _ _ seen.2
  rw [codes.2.1] at first
  have left : atSite a renumberedSite = some (.pseudoasymmetric .s) := by
    cases h : atSite a renumberedSite with
    | none => simp [h,labelCode] at first
    | some d =>
      cases d with
      | chiral k | pseudoasymmetric k => cases k <;> simp_all [labelCode]
  rw [codes.2.2.2,fixed renumberedSite reflectedRenumberedSite mirrors_rn left] at last
  contradiction

/-- Membership in the recorded finite suite. The unconditional contradiction
below thus needs no witness parameter asserting that the suite exists. -/
def suiteObservation (p : Site) (ls : List Molecular.Layout) : Prop := (p,ls) ∈ sample

private theorem suite_includes : IncludesSpiro suiteObservation := by
  simp [IncludesSpiro,suiteObservation,sample]

theorem no_universal_assignment :
    (¬ ∃ a : Assignment, Faithful suiteObservation a ∧ RelabelInvariant a) ∧
    (¬ ∃ a : Assignment, Faithful suiteObservation a ∧
      (∀ p q, Reflects p q → atSite a p = some (.pseudoasymmetric .s) →
        atSite a q = some (.pseudoasymmetric .s))) :=
  ⟨(universal_incompatibility _ suite_includes).1,
    no_lower_s_and_fidelity _ ⟨suite_includes.2.1,suite_includes.2.2.2⟩⟩

end TetraStereo.Engine.RingUniversalCompatibility

assert_kernel_only TetraStereo.Engine.RingUniversalCompatibility.universal_incompatibility
assert_kernel_only TetraStereo.Engine.RingUniversalCompatibility.sharp_spiro_bound
assert_kernel_only TetraStereo.Engine.RingUniversalCompatibility.no_universal_assignment
