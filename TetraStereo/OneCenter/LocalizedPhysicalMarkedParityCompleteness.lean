import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Complete joint-parity criterion for physical branch transport

For one molecular automorphism, the products of transported configuration signs at every pair
of reached centres determine whether its local signs admit one common proper or mirror sense.
An anchor centre then determines that sense. Empty branches are included.

Unlike a scalar R/S label at each recursively refused occurrence, these products retain the
joint parity exposed by the ring counterexamples. This theorem is an exact characterization
of the existing independent physical relation on arbitrary molecular graphs. It supplies no
CIP priority and does not assert that the current evaluator retains this complete information.
Crucially, a single automorphism must preserve all products simultaneously.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness

open RootedTetrahedralBranchSymmetry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Source configuration sign after the candidate's actual local frame permutation. -/
def transportedSign (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) : ℝ :=
  m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)

/-- The local proper/mirror sense demanded by one centre under this same candidate. -/
def relativeSign (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) : ℝ :=
  transportedSign m cfg e d * m.configurationSign cfg (m.centerPerm e d)

theorem relativeSign_eq_one_or_neg_one (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) :
    relativeSign m cfg e d = 1 ∨ relativeSign m cfg e d = -1 := by
  simpa [relativeSign, transportedSign, MultiCenterMolecule.configurationSign,
    permHandedness_mul] using
    permHandedness_eq_one_or_eq_neg_one
      (cfg d * m.ligandPermAt e d * cfg (m.centerPerm e d))

theorem relativeSign_eq_iff (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) (sense : ℝ) :
    relativeSign m cfg e d = sense ↔
      transportedSign m cfg e d = sense * m.configurationSign cfg (m.centerPerm e d) := by
  have square : m.configurationSign cfg (m.centerPerm e d) *
      m.configurationSign cfg (m.centerPerm e d) = 1 :=
    permHandedness_mul_self _
  constructor
  · intro h
    rw [← h, relativeSign, mul_assoc, square, mul_one]
  · intro h
    rw [relativeSign, h, mul_assoc, square, mul_one]

/-- All pair correlations, measured under the same molecular automorphism. The local frame
permutations are retained; they need not have equal parity at different centres. -/
def PairParityPreserved (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (reached : m.Center → Prop) : Prop :=
  ∀ a, reached a → ∀ b, reached b →
    transportedSign m cfg e a * transportedSign m cfg e b =
      m.configurationSign cfg (m.centerPerm e a) *
        m.configurationSign cfg (m.centerPerm e b)

private theorem four_signs (a b c d : Equiv.Perm (Fin 4)) :
    permHandedness a * permHandedness b = permHandedness c * permHandedness d ↔
      permHandedness a * permHandedness c = permHandedness b * permHandedness d := by
  rcases permHandedness_eq_one_or_eq_neg_one a with ha | ha <;>
    rcases permHandedness_eq_one_or_eq_neg_one b with hb | hb <;>
    rcases permHandedness_eq_one_or_eq_neg_one c with hc | hc <;>
    rcases permHandedness_eq_one_or_eq_neg_one d with hd | hd <;>
    norm_num [ha, hb, hc, hd]

theorem pairParityPreserved_iff_relativeSign_constant
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (reached : m.Center → Prop) :
    PairParityPreserved m cfg e reached ↔
      ∀ a, reached a → ∀ b, reached b → relativeSign m cfg e a = relativeSign m cfg e b := by
  unfold PairParityPreserved
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro b
  apply imp_congr_right
  intro _
  simpa [transportedSign, relativeSign, MultiCenterMolecule.configurationSign,
    permHandedness_mul] using
    four_signs (cfg a * m.ligandPermAt e a) (cfg b * m.ligandPermAt e b)
      (cfg (m.centerPerm e a)) (cfg (m.centerPerm e b))

/-- The complete pair profile can be represented by one anchor-to-centre column. This gives
the precise information a mark-indexed generated reader must recover, without requiring
independent R/S assignments at all the centres. -/
theorem pairParityPreserved_iff_anchor_products
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (reached : m.Center → Prop) (anchor : m.Center) (present : reached anchor) :
    PairParityPreserved m cfg e reached ↔
      ∀ d, reached d →
        transportedSign m cfg e anchor * transportedSign m cfg e d =
          m.configurationSign cfg (m.centerPerm e anchor) *
            m.configurationSign cfg (m.centerPerm e d) := by
  have pair (a b : m.Center) :
      transportedSign m cfg e a * transportedSign m cfg e b =
          m.configurationSign cfg (m.centerPerm e a) *
            m.configurationSign cfg (m.centerPerm e b) ↔
        relativeSign m cfg e a = relativeSign m cfg e b := by
    simpa [transportedSign, relativeSign, MultiCenterMolecule.configurationSign,
      permHandedness_mul] using
      four_signs (cfg a * m.ligandPermAt e a) (cfg b * m.ligandPermAt e b)
        (cfg (m.centerPerm e a)) (cfg (m.centerPerm e b))
  constructor
  · intro allPairs d hd
    exact allPairs anchor present d hd
  · intro column
    apply (pairParityPreserved_iff_relativeSign_constant m cfg e reached).mpr
    intro a ha b hb
    exact ((pair anchor a).mp (column a ha)).symm.trans ((pair anchor b).mp (column b hb))

/-- Pair correlations are sufficient, not merely necessary: there is one common mirror flag
for all reached centres. No rigidity, acyclicity, scalar auxiliary labels or runtime success
is assumed. The empty population is admitted and imposes no sense constraint. -/
theorem pairParityPreserved_iff_exists_sense
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (reached : m.Center → Prop) :
    PairParityPreserved m cfg e reached ↔
      ∃ mirror : Bool, ∀ d, reached d →
        transportedSign m cfg e d =
          (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d) := by
  rw [pairParityPreserved_iff_relativeSign_constant]
  constructor
  · intro constant
    by_cases inhabited : ∃ a, reached a
    · obtain ⟨a, ha⟩ := inhabited
      rcases relativeSign_eq_one_or_neg_one m cfg e a with positive | negative
      · refine ⟨false, fun d hd => (relativeSign_eq_iff m cfg e d 1).mp ?_⟩
        exact (constant d hd a ha).trans positive
      · refine ⟨true, fun d hd => (relativeSign_eq_iff m cfg e d (-1)).mp ?_⟩
        exact (constant d hd a ha).trans negative
    · exact ⟨false, fun d hd => False.elim (inhabited ⟨d, hd⟩)⟩
  · rintro ⟨mirror, signs⟩ a ha b hb
    exact ((relativeSign_eq_iff m cfg e a _).mpr (signs a ha)).trans
      ((relativeSign_eq_iff m cfg e b _).mpr (signs b hb)).symm

/-- One physical anchor plus all pair correlations gives the complete sign law with the
specified sense. A pairwise test must use the same candidate at every centre. -/
theorem signs_iff_pairParity_and_anchor
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (reached : m.Center → Prop) (anchor : m.Center) (present : reached anchor) (mirror : Bool) :
    (∀ d, reached d → transportedSign m cfg e d =
      (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d)) ↔
    PairParityPreserved m cfg e reached ∧
      transportedSign m cfg e anchor =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e anchor) := by
  constructor
  · intro signs
    exact ⟨(pairParityPreserved_iff_exists_sense m cfg e reached).mpr ⟨mirror, signs⟩,
      signs anchor present⟩
  · rintro ⟨pairs, anchorSign⟩ d hd
    apply (relativeSign_eq_iff m cfg e d _).mp
    exact ((pairParityPreserved_iff_relativeSign_constant m cfg e reached).mp pairs
      d hd anchor present).trans ((relativeSign_eq_iff m cfg e anchor _).mpr anchorSign)

/-- A nonempty branch's proper and mirror relations are individually recovered from the
complete correlation column and the sign at its anchor. No generated label is supplied. -/
theorem branchTransport_iff_pairParity_anchor
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (anchor : m.Center) (present : LigandBranchReaches m c i anchor.1) (mirror : Bool) :
    BranchTransport m cfg c i j mirror ↔
      ∃ e : m.Aut, m.centerPerm e c = c ∧ m.ligandPermAt e c i = j ∧
        PairParityPreserved m cfg e (fun d => LigandBranchReaches m c i d.1) ∧
          relativeSign m cfg e anchor = (if mirror then -1 else 1) := by
  constructor
  · rintro ⟨e, fixed, sent, signs⟩
    obtain ⟨pairs, atAnchor⟩ :=
      (signs_iff_pairParity_and_anchor m cfg e _ anchor present mirror).mp signs
    exact ⟨e, fixed, sent, pairs, (relativeSign_eq_iff m cfg e anchor _).mpr atAnchor⟩
  · rintro ⟨e, fixed, sent, pairs, atAnchor⟩
    exact ⟨e, fixed, sent,
      (signs_iff_pairParity_and_anchor m cfg e _ anchor present mirror).mpr
        ⟨pairs, (relativeSign_eq_iff m cfg e anchor _).mp atAnchor⟩⟩

/-- Exact characterization of physical proper-or-mirror branch equivalence. This quantifies
one graph automorphism for the entire profile, including overlapping cyclic branches. -/
theorem proper_or_mirror_iff_pairParity
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    ProperTransport m cfg c i j ∨ MirrorTransport m cfg c i j ↔
      ∃ e : m.Aut, m.centerPerm e c = c ∧ m.ligandPermAt e c i = j ∧
        PairParityPreserved m cfg e (fun d => LigandBranchReaches m c i d.1) := by
  constructor
  · intro transported
    rcases transported with ⟨e, fixed, sent, signs⟩ | ⟨e, fixed, sent, signs⟩
    · exact ⟨e, fixed, sent, (pairParityPreserved_iff_exists_sense m cfg e _).mpr
        ⟨false, signs⟩⟩
    · exact ⟨e, fixed, sent, (pairParityPreserved_iff_exists_sense m cfg e _).mpr
        ⟨true, signs⟩⟩
  · rintro ⟨e, fixed, sent, pairs⟩
    obtain ⟨mirror, signs⟩ := (pairParityPreserved_iff_exists_sense m cfg e _).mp pairs
    cases mirror with
    | false => exact Or.inl ⟨e, fixed, sent, signs⟩
    | true => exact Or.inr ⟨e, fixed, sent, signs⟩

/-- Every failed structural candidate has a two-centre parity witness. The candidate can
vary between witnesses, but the pair check itself always uses that single candidate. -/
theorem neither_transport_iff_pair_witness
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    (¬ ProperTransport m cfg c i j ∧ ¬ MirrorTransport m cfg c i j) ↔
      ∀ e : m.Aut, m.centerPerm e c = c → m.ligandPermAt e c i = j →
        ∃ a : m.Center, LigandBranchReaches m c i a.1 ∧
          ∃ b : m.Center, LigandBranchReaches m c i b.1 ∧
            transportedSign m cfg e a * transportedSign m cfg e b ≠
              m.configurationSign cfg (m.centerPerm e a) *
                m.configurationSign cfg (m.centerPerm e b) := by
  classical
  rw [← not_or, proper_or_mirror_iff_pairParity]
  simp only [PairParityPreserved, not_exists, not_and, not_forall, exists_prop]

theorem pair_witness_distinct
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut) (a b : m.Center)
    (mismatch : transportedSign m cfg e a * transportedSign m cfg e b ≠
      m.configurationSign cfg (m.centerPerm e a) *
        m.configurationSign cfg (m.centerPerm e b)) : a ≠ b := by
  intro same
  subst b
  apply mismatch
  have left : transportedSign m cfg e a * transportedSign m cfg e a = 1 := by
    simpa [transportedSign, MultiCenterMolecule.configurationSign, permHandedness_mul] using
      permHandedness_mul_self (cfg a * m.ligandPermAt e a)
  rw [left, show m.configurationSign cfg (m.centerPerm e a) *
    m.configurationSign cfg (m.centerPerm e a) = 1 from permHandedness_mul_self _]

end
end TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.relativeSign_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.relativeSign_eq_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.pairParityPreserved_iff_relativeSign_constant
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.pairParityPreserved_iff_anchor_products
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.pairParityPreserved_iff_exists_sense
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.signs_iff_pairParity_and_anchor
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.branchTransport_iff_pairParity_anchor
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.proper_or_mirror_iff_pairParity
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.neither_transport_iff_pair_witness
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness.pair_witness_distinct
