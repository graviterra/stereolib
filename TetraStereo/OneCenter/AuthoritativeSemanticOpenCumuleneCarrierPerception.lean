import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondTopologyPartition

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact source-canonical open-cumulene unit perception

The ordinary-double-bond topology partition classifies every physical bond, but a cumulene is one
whole connected path rather than one result per constituent bond.  This module supplies that
missing unit carrier.  It exhaustively filters maximal source paths by the independent open-network
conditions, normalizes the harmless path reversal, and erases duplicate normalized paths.  The
result is therefore complete by construction and contains each represented physical path only
once.
-/

/-- A maximal path lies in a branched ordinary-double network when a vertex connected to any path
atom has at least three ordinary-double neighbours. -/
def AromaticCanonicalCumulenePathBranched
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  ∃ anchor ∈ path, ∃ atom ∈ source.aromaticCanonicalAtomUniverse,
    source.AromaticCanonicalOrdinaryDoubleConnected anchor atom ∧
      3 ≤ (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length

/-- A maximal simple path is the cut-open presentation of a cyclic cumulene when its terminal
atoms are joined by an ordinary double bond. -/
def AromaticCanonicalCumulenePathCyclic
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  ∃ first middle last,
    path = first :: (middle ++ [last]) ∧
      source.AromaticCanonicalOrdinaryDoubleBond last first

/-- Normalize the chemically irrelevant reversal of a finite path by increasing endpoint source
index.  Degenerate lists are left unchanged; valid cumulene paths have at least two distinct
endpoints. -/
def aromaticCanonicalNormalizeCumulenePath
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) :
    List source.AromaticCanonicalAtom :=
  match path.head?, path.getLast? with
  | some first, some last => if first ≤ last then path else path.reverse
  | _, _ => path

/-- Independent meaning of one unoriented source-level open-chain unit assigned to one of the
P-93 analysis routes. -/
def AromaticCanonicalOpenCumuleneUnit
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  source.AromaticCanonicalMaximalOrdinaryCumulenePath path ∧
    ¬ source.AromaticCanonicalCumulenePathBranched path ∧
    ¬ source.AromaticCanonicalCumulenePathCyclic path ∧
    ∃ nonempty : path.length - 1 ≠ 0,
      BlueBookP93.Acyclic.DoubleBondAnalysisRouteApplies
        (.openChain (path.length - 1) nonempty) route

/-- Exhaustive canonical unit list for one P-93 open-chain route.  `dedup` is intentional:
the exhaustive path enumerator contains both path orientations, while a physical cumulene is one
unit. -/
noncomputable def aromaticCanonicalOpenCumuleneUnits
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute) :
    List (List source.AromaticCanonicalAtom) := by
  classical
  exact ((source.aromaticCanonicalMaximalOrdinaryCumulenePaths.filter fun path =>
    decide (source.AromaticCanonicalOpenCumuleneUnit route path)).map
      aromaticCanonicalNormalizeCumulenePath).dedup

/-- Exact membership: a retained unit is precisely the canonical orientation of an exhaustively
enumerated maximal path satisfying the independent open-network and P-93 route relation. -/
theorem mem_aromaticCanonicalOpenCumuleneUnits_iff
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (unit : List source.AromaticCanonicalAtom) :
    unit ∈ source.aromaticCanonicalOpenCumuleneUnits route ↔
      ∃ path,
        source.AromaticCanonicalOpenCumuleneUnit route path ∧
          aromaticCanonicalNormalizeCumulenePath path = unit := by
  classical
  rw [aromaticCanonicalOpenCumuleneUnits, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨path, present, identity⟩
    rw [List.mem_filter, decide_eq_true_eq,
      source.mem_aromaticCanonicalMaximalOrdinaryCumulenePaths_iff] at present
    exact ⟨path, present.2, identity⟩
  · rintro ⟨path, valid, identity⟩
    refine ⟨path, ?_, identity⟩
    rw [List.mem_filter, decide_eq_true_eq,
      source.mem_aromaticCanonicalMaximalOrdinaryCumulenePaths_iff]
    exact ⟨valid.1, valid⟩

/-- Every independently admitted open cumulene is represented by its normalized physical path. -/
theorem aromaticCanonicalNormalizeCumulenePath_mem_openUnits
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (path : List source.AromaticCanonicalAtom)
    (valid : source.AromaticCanonicalOpenCumuleneUnit route path) :
    aromaticCanonicalNormalizeCumulenePath path ∈
      source.aromaticCanonicalOpenCumuleneUnits route := by
  exact (source.mem_aromaticCanonicalOpenCumuleneUnits_iff route
    (aromaticCanonicalNormalizeCumulenePath path)).mpr ⟨path, valid, rfl⟩

/-- Normalized physical units never occur twice in one route list. -/
theorem aromaticCanonicalOpenCumuleneUnits_nodup
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute) :
    (source.aromaticCanonicalOpenCumuleneUnits route).Nodup := by
  classical
  exact List.nodup_dedup _

/-- Canonical planar odd-open-cumulene physical units. -/
noncomputable def aromaticCanonicalOddOpenCumuleneUnits
    (source : AuthoritativeChemicalInput) :
    List (List source.AromaticCanonicalAtom) :=
  source.aromaticCanonicalOpenCumuleneUnits .oddOpenCumulene

/-- Canonical axial even-open-cumulene physical units. -/
noncomputable def aromaticCanonicalEvenOpenCumuleneUnits
    (source : AuthoritativeChemicalInput) :
    List (List source.AromaticCanonicalAtom) :=
  source.aromaticCanonicalOpenCumuleneUnits .evenOpenCumulene

@[simp] theorem mem_aromaticCanonicalOddOpenCumuleneUnits_iff
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom) :
    unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits ↔
      ∃ path,
        source.AromaticCanonicalOpenCumuleneUnit .oddOpenCumulene path ∧
          aromaticCanonicalNormalizeCumulenePath path = unit := by
  exact source.mem_aromaticCanonicalOpenCumuleneUnits_iff .oddOpenCumulene unit

@[simp] theorem mem_aromaticCanonicalEvenOpenCumuleneUnits_iff
    (source : AuthoritativeChemicalInput)
    (unit : List source.AromaticCanonicalAtom) :
    unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits ↔
      ∃ path,
        source.AromaticCanonicalOpenCumuleneUnit .evenOpenCumulene path ∧
          aromaticCanonicalNormalizeCumulenePath path = unit := by
  exact source.mem_aromaticCanonicalOpenCumuleneUnits_iff .evenOpenCumulene unit

theorem aromaticCanonicalOddOpenCumuleneUnits_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalOddOpenCumuleneUnits.Nodup :=
  source.aromaticCanonicalOpenCumuleneUnits_nodup .oddOpenCumulene

theorem aromaticCanonicalEvenOpenCumuleneUnits_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalEvenOpenCumuleneUnits.Nodup :=
  source.aromaticCanonicalOpenCumuleneUnits_nodup .evenOpenCumulene

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
