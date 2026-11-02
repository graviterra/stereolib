import TetraStereo.OneCenter.CIPAuthoritativeRule6Completeness

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPCursorSupport

/-!
# Molecule-level well-founded support for the authoritative occurrence traversal

`CursorSupport` is the exact recursive invariant consumed by the uncapped comparator.  The
certificate below is its conventional molecule-level presentation: every cursor receives a finite
height, real child steps strictly decrease that height, rank zero is terminal, and every local
child list lies in the IUPAC bonding-number-six scope.  No bound is placed on a complete sphere or
on the number of paths represented by the molecular digraph.
-/

open RawMolecule
open AuthoritativeCIPRule6Completeness

/-- Molecule-level chemical admissibility of every localized mancude duplicate needed by Rule 1a.
Real atoms, ring duplicates, and phantoms have total labels by construction; this is precisely the
remaining source-sensitive case. -/
def MancudeRule1aSupported (mol : RawMolecule) : Prop :=
  ∀ attached duplicated, ∃ label,
    mol.mancudeRule1aLabelAuthoritative? attached duplicated = some label

/-- Mancude support makes the authoritative Rule-1a observation total for every canonical node. -/
theorem canonicalRule1aLabelAuthoritative?_exists (mol : RawMolecule)
    (supported : MancudeRule1aSupported mol) (node : CanonicalBranchNode) :
    ∃ label, mol.canonicalRule1aLabelAuthoritative? node = some label := by
  cases provenanceEq : node.provenance with
  | realAtom => exact ⟨{ numerator := mol.atomZAt node.atom, denominator := 1 }, by
      simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenanceEq]⟩
  | multipleBondDuplicate distance =>
      rcases supported node.parent node.atom with ⟨label, observed⟩
      exact ⟨label, by
        simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenanceEq, observed]⟩
  | ringDuplicate distance =>
      exact ⟨{ numerator := mol.atomZAt node.atom, denominator := 1 }, by
        simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenanceEq]⟩
  | phantom distance =>
      exact ⟨{ numerator := 0, denominator := 1 }, by
        simp [RawMolecule.canonicalRule1aLabelAuthoritative?, provenanceEq]⟩

/-- A well-founded finite-height certificate for one molecule's complete reroot occurrence
digraph.  `height` is semantic evidence, not operational fuel: it may be any decreasing ranking. -/
structure CursorTerminationRanking (mol : RawMolecule) where
  eligible : CanonicalRerootCursor → Prop
  height : CanonicalRerootCursor → Nat
  zero_terminal : ∀ cursor : CanonicalRerootCursor,
    eligible cursor → height cursor = 0 → cursorTerminal mol cursor = true
  local_width : ∀ cursor : CanonicalRerootCursor,
    eligible cursor → (cursor.children mol).length ≤ RawMolecule.authoritativeChildSlots
  child_eligible : ∀ cursor child : CanonicalRerootCursor,
    eligible cursor → child ∈ cursor.children mol → eligible child
  child_decreases : ∀ cursor child : CanonicalRerootCursor,
    eligible cursor → child ∈ cursor.children mol → height child < height cursor

namespace CursorTerminationRanking

/-- A decreasing molecule-level height supplies the exact recursive support consumed by every
authoritative sphere traversal. -/
theorem cursorSupport {mol : RawMolecule} (ranking : CursorTerminationRanking mol)
    (cursor : CanonicalRerootCursor) (eligible : ranking.eligible cursor) :
    CursorSupport mol (ranking.height cursor) cursor := by
  by_cases terminal : cursorTerminal mol cursor = true
  · exact .terminal (ranking.height cursor) cursor terminal
  · cases heightEq : ranking.height cursor with
    | zero =>
        exact False.elim (terminal (ranking.zero_terminal cursor eligible heightEq))
    | succ height =>
        apply CursorSupport.branch height cursor (cursor.children mol) rfl
          (ranking.local_width cursor eligible)
        intro child member
        have childEligible := ranking.child_eligible cursor child eligible member
        have decrease := ranking.child_decreases cursor child eligible member
        have childSupport := ranking.cursorSupport child childEligible
        exact childSupport.mono (by omega)
termination_by ranking.height cursor

/-- Any caller fuel covering the certified molecular height supplies recursive cursor support. -/
theorem cursorSupport_of_height_le {mol : RawMolecule}
    (ranking : CursorTerminationRanking mol) (fuel : Nat)
    (cursor : CanonicalRerootCursor) (eligible : ranking.eligible cursor)
    (covered : ranking.height cursor ≤ fuel) :
    CursorSupport mol fuel cursor :=
  (ranking.cursorSupport cursor eligible).mono covered

/-- Pointwise height coverage lifts to a whole finite list of physical ligand roots. -/
theorem roots_supported {mol : RawMolecule} (ranking : CursorTerminationRanking mol)
    (fuel : Nat) (roots : List CanonicalRerootCursor)
    (eligible : ∀ root, root ∈ roots → ranking.eligible root)
    (covered : ∀ root, root ∈ roots → ranking.height root ≤ fuel) :
    ∀ root, root ∈ roots → CursorSupport mol fuel root := by
  intro root member
  exact ranking.cursorSupport_of_height_le fuel root (eligible root member) (covered root member)

end CursorTerminationRanking

end TetraStereo.OneCenter.AuthoritativeCIPCursorSupport
