import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60SourceData
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70SourceData
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76SourceData
import TetraStereo.KernelOnly
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

/-!
# Frozen attachment placements for the five P-93.5.6 derivatives

This source-only leaf records exactly the constitutional addend kinds and cage locants printed on
Blue Book PDF pages 80--83.  Printed locant `k` is stored as cage atom `k - 1`.  Multiport
cyclopropano addends remain one placement with two attachment sites; they are not flattened into
unary site colors.

The molecule graphs of the addend kinds are intentionally not declared here.  They belong in the
separately audited template source.  This file freezes only the placement boundary which that
template compiler consumes.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

/-- Constitutional addend kinds occurring in the five printed derivative examples. -/
inductive IUPACP93PrintedFullereneAddendKind where
  | hydrogen
  | tertButyl
  | trisilyl
  | dicyclopropylCycloheptatrienyl
  | cyclopropanoBisCarboxylatePhenylbutyl
  deriving DecidableEq, Repr

/-- One printed whole-addend placement.  A two-site finset is one bidentate addend, not two
independent substituents. -/
structure IUPACP93PrintedFullereneAddendPlacement where
  kind : IUPACP93PrintedFullereneAddendKind
  attachmentSites : Finset Nat
  deriving DecidableEq

namespace IUPACP93PrintedFullereneAddendPlacement

def ValidForAtomCount (atomCount : Nat)
    (placement : IUPACP93PrintedFullereneAddendPlacement) : Prop :=
  placement.attachmentSites.Nonempty ∧
    placement.attachmentSites ⊆ Finset.range atomCount

end IUPACP93PrintedFullereneAddendPlacement



def IUPACP93PrintedFullereneAddendPlacementsJudgment
    (atomCount : Nat)
    (placements : List IUPACP93PrintedFullereneAddendPlacement) : Prop :=
  placements ≠ [] ∧ placements.Nodup ∧
    (∀ placement ∈ placements, placement.ValidForAtomCount atomCount) ∧
    placements.Pairwise fun first second =>
      Disjoint first.attachmentSites second.attachmentSites

/-- Page 80, P-93.5.6.2 example II:
`20-tert-butyl-20,21-dihydro(C76-D2)[5,6]fullerene`. -/
def iupacP93CanonicalFullereneC76Type1Placements :
    List IUPACP93PrintedFullereneAddendPlacement :=
  [ { kind := .tertButyl, attachmentSites := {19} }
  , { kind := .hydrogen, attachmentSites := {20} }
  ]

/-- Page 81, P-93.5.6.3: identical trisilyl addends at printed locants 1 and 23. -/
def iupacP93CanonicalFullereneC60Type2Placements :
    List IUPACP93PrintedFullereneAddendPlacement :=
  [ { kind := .trisilyl, attachmentSites := {0} }
  , { kind := .trisilyl, attachmentSites := {22} }
  ]

/-- Page 81, P-93.5.6.4: constitutionally different tert-butyl and
3,6-dicyclopropylcycloheptatrienyl addends at printed locants 1 and 7. -/
def iupacP93CanonicalFullereneC60Type3Placements :
    List IUPACP93PrintedFullereneAddendPlacement :=
  [ { kind := .tertButyl, attachmentSites := {0} }
  , { kind := .dicyclopropylCycloheptatrienyl, attachmentSites := {6} }
  ]

/-- Page 82, P-93.5.6.5: two identical bidentate cyclopropano addends at printed locant pairs
`8,25` and `16,35`. -/
def iupacP93CanonicalFullereneC70Type4Placements :
    List IUPACP93PrintedFullereneAddendPlacement :=
  [ { kind := .cyclopropanoBisCarboxylatePhenylbutyl,
      attachmentSites := {7, 24} }
  , { kind := .cyclopropanoBisCarboxylatePhenylbutyl,
      attachmentSites := {15, 34} }
  ]

/-- Page 83, P-93.5.6.6: two identical bidentate cyclopropano addends at printed locant pairs
`8,25` and `33,34`. -/
def iupacP93CanonicalFullereneC70SuperimposedPlacements :
    List IUPACP93PrintedFullereneAddendPlacement :=
  [ { kind := .cyclopropanoBisCarboxylatePhenylbutyl,
      attachmentSites := {7, 24} }
  , { kind := .cyclopropanoBisCarboxylatePhenylbutyl,
      attachmentSites := {32, 33} }
  ]

theorem iupacP93CanonicalFullereneC76Type1Placements_audited :
    IUPACP93PrintedFullereneAddendPlacementsJudgment 76
      iupacP93CanonicalFullereneC76Type1Placements := by
  simp [IUPACP93PrintedFullereneAddendPlacementsJudgment,
    iupacP93CanonicalFullereneC76Type1Placements,
    IUPACP93PrintedFullereneAddendPlacement.ValidForAtomCount,
    Finset.disjoint_left]

theorem iupacP93CanonicalFullereneC60Type2Placements_audited :
    IUPACP93PrintedFullereneAddendPlacementsJudgment 60
      iupacP93CanonicalFullereneC60Type2Placements := by
  simp [IUPACP93PrintedFullereneAddendPlacementsJudgment,
    iupacP93CanonicalFullereneC60Type2Placements,
    IUPACP93PrintedFullereneAddendPlacement.ValidForAtomCount,
    Finset.disjoint_left]

theorem iupacP93CanonicalFullereneC60Type3Placements_audited :
    IUPACP93PrintedFullereneAddendPlacementsJudgment 60
      iupacP93CanonicalFullereneC60Type3Placements := by
  simp [IUPACP93PrintedFullereneAddendPlacementsJudgment,
    iupacP93CanonicalFullereneC60Type3Placements,
    IUPACP93PrintedFullereneAddendPlacement.ValidForAtomCount,
    Finset.disjoint_left]

theorem iupacP93CanonicalFullereneC70Type4Placements_audited :
    IUPACP93PrintedFullereneAddendPlacementsJudgment 70
      iupacP93CanonicalFullereneC70Type4Placements := by
  simp [IUPACP93PrintedFullereneAddendPlacementsJudgment,
    iupacP93CanonicalFullereneC70Type4Placements,
    IUPACP93PrintedFullereneAddendPlacement.ValidForAtomCount,
    Finset.disjoint_left]
  decide

theorem iupacP93CanonicalFullereneC70SuperimposedPlacements_audited :
    IUPACP93PrintedFullereneAddendPlacementsJudgment 70
      iupacP93CanonicalFullereneC70SuperimposedPlacements := by
  simp [IUPACP93PrintedFullereneAddendPlacementsJudgment,
    iupacP93CanonicalFullereneC70SuperimposedPlacements,
    IUPACP93PrintedFullereneAddendPlacement.ValidForAtomCount,
    Finset.disjoint_left]
  decide


theorem iupacP93CanonicalFullereneDerivativePlacementsAudited :
    IUPACP93PrintedFullereneAddendPlacementsJudgment 76
        iupacP93CanonicalFullereneC76Type1Placements ∧
      IUPACP93PrintedFullereneAddendPlacementsJudgment 60
        iupacP93CanonicalFullereneC60Type2Placements ∧
      IUPACP93PrintedFullereneAddendPlacementsJudgment 60
        iupacP93CanonicalFullereneC60Type3Placements ∧
      IUPACP93PrintedFullereneAddendPlacementsJudgment 70
        iupacP93CanonicalFullereneC70Type4Placements ∧
      IUPACP93PrintedFullereneAddendPlacementsJudgment 70
        iupacP93CanonicalFullereneC70SuperimposedPlacements := by
  exact ⟨iupacP93CanonicalFullereneC76Type1Placements_audited,
    iupacP93CanonicalFullereneC60Type2Placements_audited,
    iupacP93CanonicalFullereneC60Type3Placements_audited,
    iupacP93CanonicalFullereneC70Type4Placements_audited,
    iupacP93CanonicalFullereneC70SuperimposedPlacements_audited⟩

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDerivativePlacementsAudited
