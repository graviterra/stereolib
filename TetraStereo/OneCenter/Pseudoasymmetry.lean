import TetraStereo.OneCenter.CIPFrontier
import TetraStereo.OneCenter.MultiCenterRS

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Rule-5-facing pseudoasymmetry scaffold.

  Full CIP pseudoasymmetry is subtler than ordinary one-center `R/S`: a tetrahedral unit can
  receive a lowercase `r/s` descriptor when two otherwise tied ligand paths are enantiomorphic.
  The key cancellation is formalized here: mirror reflection negates the local tetrahedral
  handedness, but also swaps the enantiomorphic `R/S` ligand labels, so the lowercase descriptor is
  reflection-invariant.

  ## Sign calibration (source view)

  The IUPAC source convention (Blue Book P-92.1.2.1, preferred viewing side remote from the
  lowest-precedence ligand) reads **clockwise** as `R` (or pseudoasymmetric `r`).  In the standard
  right-handed Cartesian frame (`x` right, `y` up, `z` toward the viewer) the determinant of the
  four priority slots `[highest, left, right, lowest]` is **negative** precisely in that clockwise
  case (see `TetraStereo/OneCenter/PseudoTetrahedralViewingFidelity.lean`).  Therefore the
  determinant-based sign `-1` is the `r` sign and `+1` is the `s` sign.

  `pseudoasymmetricSign` multiplies that local sign by the Rule-5 orientation of the
  enantiomorphic pair (`R` before `S` is `+1`).  The corrected `PseudoRS.ofSign` below maps
  `-1 ↦ r` and everything else (in particular `+1` and the degenerate fallback `0`) to `s`.
-/

/-- Lowercase pseudoasymmetric descriptors. -/
inductive PseudoRS where
  | r
  | s
  deriving DecidableEq, Repr

namespace PseudoRS

/-- Convert a normalized pseudoasymmetric sign to a lowercase descriptor.

Calibration (source viewing, remote from the lowest-precedence ligand, clockwise = lowercase `r`):
`-1 ↦ r`, `+1 ↦ s`.

The definition is total.  Any value other than `-1` — in particular the degenerate sign `0` —
takes the explicit safe fallback `s`; descriptor callers only use nondegenerate signs, which are
`-1` or `+1` (see `Normalized` below). -/
def ofSign (h : ℝ) : PseudoRS :=
  if h = -1 then PseudoRS.r else PseudoRS.s

@[simp] theorem ofSign_neg_one : ofSign (-1) = PseudoRS.r := by
  simp [ofSign]

@[simp] theorem ofSign_one : ofSign 1 = PseudoRS.s := by
  have h : (1 : ℝ) ≠ -1 := by norm_num
  simp [ofSign, h]

@[simp] theorem ofSign_zero : ofSign 0 = PseudoRS.s := by
  have h : (0 : ℝ) ≠ -1 := by norm_num
  simp [ofSign, h]

/-- Total fallback: any sign other than `-1` is read as `s`. -/
theorem ofSign_eq_s_of_ne_neg_one {h : ℝ} (hh : h ≠ -1) : ofSign h = PseudoRS.s := by
  simp [ofSign, hh]

/-- Exact characterization of the `r` sign. -/
theorem ofSign_eq_r_iff {h : ℝ} : ofSign h = PseudoRS.r ↔ h = -1 := by
  constructor
  · intro hr
    by_contra hh
    have hsr : ofSign h = PseudoRS.s := by simp [ofSign, hh]
    rw [hsr] at hr
    cases hr
  · intro hh
    simp [ofSign, hh]

/-- Exact characterization of the `s` sign. -/
theorem ofSign_eq_s_iff {h : ℝ} : ofSign h = PseudoRS.s ↔ h ≠ -1 := by
  constructor
  · intro hs hh
    have hr : ofSign h = PseudoRS.r := by simp [ofSign, hh]
    rw [hr] at hs
    cases hs
  · intro hh
    simp [ofSign, hh]

/-- Nondegenerate signs of the source calibration. -/
def Normalized (h : ℝ) : Prop :=
  h = -1 ∨ h = 1

theorem normalized_neg {h : ℝ} (hh : Normalized h) : Normalized (-h) := by
  rcases hh with rfl | rfl
  · exact Or.inr (by norm_num)
  · exact Or.inl (by norm_num)

theorem normalized_of_eq_neg_one {h : ℝ} (hh : h = -1) : Normalized h :=
  Or.inl hh

theorem normalized_of_eq_one {h : ℝ} (hh : h = 1) : Normalized h :=
  Or.inr hh

end PseudoRS

/-- Rule-5 orientation of an enantiomorphic ligand pair.  We use `R` before `S` as positive. -/
def rule5PairSign : RS → RS → ℝ
  | RS.R, RS.S => 1
  | RS.S, RS.R => -1
  | _, _ => 0

@[simp] theorem rule5PairSign_R_S : rule5PairSign RS.R RS.S = 1 := rfl

@[simp] theorem rule5PairSign_S_R : rule5PairSign RS.S RS.R = -1 := rfl

@[simp] theorem rule5PairSign_R_R : rule5PairSign RS.R RS.R = 0 := rfl

@[simp] theorem rule5PairSign_S_S : rule5PairSign RS.S RS.S = 0 := rfl

@[simp] theorem rule5PairSign_swap_swap (left right : RS) :
    rule5PairSign (RS.swap left) (RS.swap right) = -rule5PairSign left right := by
  cases left <;> cases right <;> simp [rule5PairSign, RS.swap]

/-- Convert a comparison outcome to the sign convention used by descriptor-dependent Rule 5:
`gt` means the left ligand has positive priority orientation, `lt` negative, and `eq` unresolved. -/
def orderingSign : Ordering → ℝ
  | Ordering.gt => 1
  | Ordering.lt => -1
  | Ordering.eq => 0

@[simp] theorem orderingSign_gt : orderingSign Ordering.gt = 1 := rfl

@[simp] theorem orderingSign_lt : orderingSign Ordering.lt = -1 := rfl

@[simp] theorem orderingSign_eq : orderingSign Ordering.eq = 0 := rfl

/-- Rule-5 comparison outcome for two enantiomorphic ligand descriptors, comparing the left ligand
against the right ligand. -/
def rule5PairOrdering : RS → RS → Ordering
  | RS.R, RS.S => Ordering.gt
  | RS.S, RS.R => Ordering.lt
  | _, _ => Ordering.eq

@[simp] theorem orderingSign_rule5PairOrdering (left right : RS) :
    orderingSign (rule5PairOrdering left right) = rule5PairSign left right := by
  cases left <;> cases right <;> simp [orderingSign, rule5PairOrdering, rule5PairSign]

/-- The rule-trace decision corresponding to an enantiomorphic-ligand Rule-5 tiebreak. -/
def rule5PairDecision (left right : RS) : CIPRuleDecision where
  rule := CIPRuleFamily.pseudoasymmetricTiebreak
  outcome := rule5PairOrdering left right

/-- A one-step trace certificate for a Rule-5 enantiomorphic-ligand comparison. -/
def rule5PairTraceCertificate (left right : RS) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace [rule5PairDecision left right]

@[simp] theorem rule5PairOrdering_R_S : rule5PairOrdering RS.R RS.S = Ordering.gt := rfl

@[simp] theorem rule5PairOrdering_S_R : rule5PairOrdering RS.S RS.R = Ordering.lt := rfl

@[simp] theorem rule5PairTraceCertificate_R_S_outcome :
    (rule5PairTraceCertificate RS.R RS.S).outcome = Ordering.gt := by
  simp [rule5PairTraceCertificate, rule5PairDecision, CIPTraceCertificate.ofTrace,
    cipTraceOutcome, rule5PairOrdering]

@[simp] theorem rule5PairTraceCertificate_S_R_outcome :
    (rule5PairTraceCertificate RS.S RS.R).outcome = Ordering.lt := by
  simp [rule5PairTraceCertificate, rule5PairDecision, CIPTraceCertificate.ofTrace,
    cipTraceOutcome, rule5PairOrdering]

/-- The pseudoasymmetric sign combines local central handedness with the Rule-5 orientation of the
enantiomorphic ligand pair. -/
def pseudoasymmetricSign (centerSign : ℝ) (left right : RS) : ℝ :=
  centerSign * rule5PairSign left right

/-- Lowercase descriptor read from the pseudoasymmetric sign. -/
def pseudoDescriptor (centerSign : ℝ) (left right : RS) : PseudoRS :=
  PseudoRS.ofSign (pseudoasymmetricSign centerSign left right)

/-- The exact `r` criterion for the lowercase producer: the combined sign is `-1`. -/
theorem pseudoDescriptor_eq_r_iff (centerSign : ℝ) (left right : RS) :
    pseudoDescriptor centerSign left right = PseudoRS.r ↔
      pseudoasymmetricSign centerSign left right = -1 := by
  simp [pseudoDescriptor, PseudoRS.ofSign_eq_r_iff]

/-- The exact `s` criterion for the lowercase producer: the combined sign is not `-1`. -/
theorem pseudoDescriptor_eq_s_iff (centerSign : ℝ) (left right : RS) :
    pseudoDescriptor centerSign left right = PseudoRS.s ↔
      pseudoasymmetricSign centerSign left right ≠ -1 := by
  simp [pseudoDescriptor, PseudoRS.ofSign_eq_s_iff]

/-- The producer is total: every input yields either `r` or `s`. -/
theorem pseudoDescriptor_eq_r_or_s (centerSign : ℝ) (left right : RS) :
    pseudoDescriptor centerSign left right = PseudoRS.r ∨
      pseudoDescriptor centerSign left right = PseudoRS.s := by
  by_cases h : pseudoasymmetricSign centerSign left right = -1
  · exact Or.inl ((pseudoDescriptor_eq_r_iff centerSign left right).2 h)
  · exact Or.inr ((pseudoDescriptor_eq_s_iff centerSign left right).2 h)

/-- Zero total sign preserves the explicit safe fallback `s`. -/
@[simp] theorem pseudoDescriptor_zero (left right : RS) :
    pseudoDescriptor 0 left right = PseudoRS.s := by
  simp [pseudoDescriptor, pseudoasymmetricSign]

theorem pseudoasymmetricSign_mirror (centerSign : ℝ) (left right : RS) :
    pseudoasymmetricSign (-centerSign) (RS.swap left) (RS.swap right) =
      pseudoasymmetricSign centerSign left right := by
  simp [pseudoasymmetricSign]

theorem pseudoDescriptor_mirror (centerSign : ℝ) (left right : RS) :
    pseudoDescriptor (-centerSign) (RS.swap left) (RS.swap right) =
      pseudoDescriptor centerSign left right := by
  simp [pseudoDescriptor, pseudoasymmetricSign_mirror]

/-! ### Corrected concrete signs

The four normalized source cases.  Note that `r` is the negative combined sign in every case;
a positive combined sign is `s`.  The two `r` cases are mirror images of one another. -/

@[simp] theorem pseudoDescriptor_negOne_R_S :
    pseudoDescriptor (-1) RS.R RS.S = PseudoRS.r := by
  simp [pseudoDescriptor, pseudoasymmetricSign]

@[simp] theorem pseudoDescriptor_one_R_S :
    pseudoDescriptor 1 RS.R RS.S = PseudoRS.s := by
  simp [pseudoDescriptor, pseudoasymmetricSign]

@[simp] theorem pseudoDescriptor_one_S_R :
    pseudoDescriptor 1 RS.S RS.R = PseudoRS.r := by
  simp [pseudoDescriptor, pseudoasymmetricSign]

@[simp] theorem pseudoDescriptor_negOne_S_R :
    pseudoDescriptor (-1) RS.S RS.R = PseudoRS.s := by
  simp [pseudoDescriptor, pseudoasymmetricSign]

/-- A compact certificate for a pseudoasymmetric center inside a multi-center molecule.  It records
the central local handedness, the enantiomorphic side descriptors, the resulting lowercase
descriptor, and a symmetry proof that the full configuration is achiral. -/
structure PseudoasymmetricRule5Certificate {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) where
  center : m.Center
  centerSign : ℝ
  centerSign_normalized : PseudoRS.Normalized centerSign
  leftDescriptor : RS
  rightDescriptor : RS
  centerSign_eq : m.configurationSign cfg center = centerSign
  enantiomorphic : rightDescriptor = RS.swap leftDescriptor
  descriptor : PseudoRS
  descriptor_eq : descriptor = pseudoDescriptor centerSign leftDescriptor rightDescriptor
  achiral : m.AchiralConfigurationBySymmetry cfg

namespace PseudoasymmetricRule5Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

theorem descriptor_mirror_invariant
    (cert : PseudoasymmetricRule5Certificate m cfg) :
    pseudoDescriptor (-cert.centerSign) (RS.swap cert.leftDescriptor)
      (RS.swap cert.rightDescriptor) = cert.descriptor := by
  rw [pseudoDescriptor_mirror, cert.descriptor_eq]

/-- The certificate's lowercase descriptor is `r` exactly when the combined source sign is `-1`. -/
theorem descriptor_eq_r_iff
    (cert : PseudoasymmetricRule5Certificate m cfg) :
    cert.descriptor = PseudoRS.r ↔
      cert.centerSign * rule5PairSign cert.leftDescriptor cert.rightDescriptor = -1 := by
  rw [cert.descriptor_eq, pseudoDescriptor_eq_r_iff]
  rfl

/-- The certificate's lowercase descriptor is total. -/
theorem descriptor_eq_r_or_s
    (cert : PseudoasymmetricRule5Certificate m cfg) :
    cert.descriptor = PseudoRS.r ∨ cert.descriptor = PseudoRS.s := by
  rw [cert.descriptor_eq]
  exact pseudoDescriptor_eq_r_or_s cert.centerSign cert.leftDescriptor cert.rightDescriptor

end PseudoasymmetricRule5Certificate

end
end OneCenter
end TetraStereo
