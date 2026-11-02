import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOrdinaryCumuleneEnumeration
import TetraStereo.OneCenter.P93AcyclicConfiguration
import Mathlib.Data.List.MinMax

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Canonical source-level partition of ordinary double-bond networks

This module supplies the missing global carrier between exhaustive source-canonical ordinary
double-bond perception and the independent P-93 routing theorem.  Every physical nonaromatic
order-two bond is enumerated once, its connected order-two network is classified without choosing
an arbitrary local arm, and the bond is placed in exactly one of five analysis-owner lists.
-/

/-- An undirected physical step occurs consecutively in a finite atom path. -/
def AromaticCanonicalPathContainsBond
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom)
    (left right : source.AromaticCanonicalAtom) : Prop :=
  ∃ before after,
    path = before ++ left :: right :: after ∨
      path = before ++ right :: left :: after

theorem aromaticCanonicalPathContainsBond_pair
    {source : AuthoritativeChemicalInput}
    (left right : source.AromaticCanonicalAtom) :
    AromaticCanonicalPathContainsBond [left, right] left right := by
  exact ⟨[], [], Or.inl rfl⟩

theorem AromaticCanonicalPathContainsBond.length_two_le
    {source : AuthoritativeChemicalInput}
    {path : List source.AromaticCanonicalAtom}
    {left right : source.AromaticCanonicalAtom}
    (contains : AromaticCanonicalPathContainsBond path left right) :
    2 ≤ path.length := by
  rcases contains with ⟨before, after, forward | reverse⟩ <;>
    subst path <;> simp <;> omega

theorem AromaticCanonicalPathContainsBond.cons
    {source : AuthoritativeChemicalInput}
    {path : List source.AromaticCanonicalAtom}
    {left right : source.AromaticCanonicalAtom}
    (contains : AromaticCanonicalPathContainsBond path left right)
    (atom : source.AromaticCanonicalAtom) :
    AromaticCanonicalPathContainsBond (atom :: path) left right := by
  rcases contains with ⟨before, after, forward | reverse⟩
  · exact ⟨atom :: before, after, Or.inl (by simp [forward])⟩
  · exact ⟨atom :: before, after, Or.inr (by simp [reverse])⟩

theorem AromaticCanonicalPathContainsBond.append
    {source : AuthoritativeChemicalInput}
    {path : List source.AromaticCanonicalAtom}
    {left right : source.AromaticCanonicalAtom}
    (contains : AromaticCanonicalPathContainsBond path left right)
    (atom : source.AromaticCanonicalAtom) :
    AromaticCanonicalPathContainsBond (path ++ [atom]) left right := by
  rcases contains with ⟨before, after, forward | reverse⟩
  · exact ⟨before, after ++ [atom], Or.inl (by simp [forward, List.append_assoc])⟩
  · exact ⟨before, after ++ [atom], Or.inr (by simp [reverse, List.append_assoc])⟩

/-- Every source-canonical ordinary physical double bond exactly once, oriented by strict source
atom order. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondPairs
    (source : AuthoritativeChemicalInput) :
    List (source.AromaticCanonicalAtom × source.AromaticCanonicalAtom) := by
  classical
  exact (source.aromaticCanonicalAtomUniverse ×ˢ
    source.aromaticCanonicalAtomUniverse).filter fun pair =>
      decide (pair.1 < pair.2 ∧
        source.AromaticCanonicalOrdinaryDoubleBond pair.1 pair.2)

@[simp] theorem mem_aromaticCanonicalOrdinaryDoubleBondPairs_iff
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    (left, right) ∈ source.aromaticCanonicalOrdinaryDoubleBondPairs ↔
      left < right ∧ source.AromaticCanonicalOrdinaryDoubleBond left right := by
  classical
  simp [aromaticCanonicalOrdinaryDoubleBondPairs]

theorem aromaticCanonicalOrdinaryDoubleBondPairs_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalOrdinaryDoubleBondPairs.Nodup := by
  classical
  exact (source.aromaticCanonicalAtomUniverse_nodup.product
    source.aromaticCanonicalAtomUniverse_nodup).filter _

/-- Proof-relevant canonical source ordinary-double-bond carrier. -/
abbrev AromaticCanonicalOrdinaryDoubleBondCarrier
    (source : AuthoritativeChemicalInput) :=
  { pair : source.AromaticCanonicalAtom × source.AromaticCanonicalAtom //
    pair ∈ source.aromaticCanonicalOrdinaryDoubleBondPairs }

namespace AromaticCanonicalOrdinaryDoubleBondCarrier

def left {source : AuthoritativeChemicalInput}
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.AromaticCanonicalAtom := bond.1.1

def right {source : AuthoritativeChemicalInput}
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.AromaticCanonicalAtom := bond.1.2

theorem ordered {source : AuthoritativeChemicalInput}
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond.left < bond.right :=
  (source.mem_aromaticCanonicalOrdinaryDoubleBondPairs_iff
    bond.left bond.right).mp bond.2 |>.1

theorem ordinary {source : AuthoritativeChemicalInput}
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.AromaticCanonicalOrdinaryDoubleBond bond.left bond.right :=
  (source.mem_aromaticCanonicalOrdinaryDoubleBondPairs_iff
    bond.left bond.right).mp bond.2 |>.2

end AromaticCanonicalOrdinaryDoubleBondCarrier

/-- Every simple ordinary-double path containing this physical bond. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondPathsContaining
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    List (List source.AromaticCanonicalAtom) := by
  classical
  exact source.aromaticCanonicalOrdinaryCumulenePaths.filter fun path =>
    decide (AromaticCanonicalPathContainsBond path bond.left bond.right)

theorem mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (path : List source.AromaticCanonicalAtom) :
    path ∈ source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond ↔
      source.AromaticCanonicalOrdinaryCumulenePath path ∧
        AromaticCanonicalPathContainsBond path bond.left bond.right := by
  classical
  simp [aromaticCanonicalOrdinaryDoubleBondPathsContaining,
    source.mem_aromaticCanonicalOrdinaryCumulenePaths_iff]

theorem pair_mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    [bond.left, bond.right] ∈
      source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond := by
  rw [source.mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining_iff]
  refine ⟨?_, aromaticCanonicalPathContainsBond_pair bond.left bond.right⟩
  constructor
  · simp [ne_of_lt bond.ordered]
  · simpa using bond.ordinary

/-- The finite nonempty candidate list has a maximum-length member. -/
theorem exists_aromaticCanonicalOrdinaryDoubleBondArgmaxPath
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    ∃ path, (source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond).argmax
      (fun candidate : List source.AromaticCanonicalAtom => candidate.length) = some path := by
  cases computed : (source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond).argmax
      (fun candidate : List source.AromaticCanonicalAtom => candidate.length) with
  | none =>
      have empty := List.argmax_eq_none.mp computed
      exact ((List.ne_nil_of_mem
        (source.pair_mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining bond)) empty).elim
  | some path => exact ⟨path, rfl⟩

/-- Deterministic maximum-length simple ordinary-double path containing the bond.  Enumeration
order resolves the harmless reversal tie. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondCanonicalPath
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    List source.AromaticCanonicalAtom :=
  Classical.choose (source.exists_aromaticCanonicalOrdinaryDoubleBondArgmaxPath bond)

theorem aromaticCanonicalOrdinaryDoubleBondCanonicalPath_computed
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond).argmax
        (fun candidate : List source.AromaticCanonicalAtom => candidate.length) =
      some (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond) :=
  Classical.choose_spec (source.exists_aromaticCanonicalOrdinaryDoubleBondArgmaxPath bond)

theorem aromaticCanonicalOrdinaryDoubleBondCanonicalPath_mem
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond ∈
      source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond := by
  apply List.argmax_mem
    (f := fun candidate : List source.AromaticCanonicalAtom => candidate.length)
  simp [source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_computed bond]

theorem aromaticCanonicalOrdinaryDoubleBondCanonicalPath_valid
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.AromaticCanonicalOrdinaryCumulenePath
        (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond) ∧
      AromaticCanonicalPathContainsBond
        (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond)
        bond.left bond.right :=
  (source.mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining_iff
    bond (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond)).mp
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_mem bond)

theorem aromaticCanonicalOrdinaryDoubleBondCanonicalPath_maximal_length
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (path : List source.AromaticCanonicalAtom)
    (present : path ∈ source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond) :
    path.length ≤
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length := by
  apply List.le_of_mem_argmax present
  simp [source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_computed bond]

theorem aromaticCanonicalOrdinaryDoubleBondCanonicalPath_length_two_le
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    2 ≤ (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length :=
  (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_valid bond).2.length_two_le

/-- Maximum length makes the chosen path genuinely endpoint-maximal, not merely an arbitrary
simple path through the bond. -/
theorem aromaticCanonicalOrdinaryDoubleBondCanonicalPath_maximal
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.AromaticCanonicalMaximalOrdinaryCumulenePath
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond) := by
  let path := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond
  have valid := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_valid bond
  refine ⟨source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_length_two_le bond,
    valid.1, ?_, ?_⟩
  · intro atom extended
    have present : atom :: path ∈
        source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond :=
      (source.mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining_iff
        bond (atom :: path)).mpr ⟨extended, valid.2.cons atom⟩
    have bounded :=
      source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_maximal_length
        bond (atom :: path) present
    simp [path] at bounded
  · intro atom extended
    have present : path ++ [atom] ∈
        source.aromaticCanonicalOrdinaryDoubleBondPathsContaining bond :=
      (source.mem_aromaticCanonicalOrdinaryDoubleBondPathsContaining_iff
        bond (path ++ [atom])).mpr ⟨extended, valid.2.append atom⟩
    have bounded :=
      source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_maximal_length
        bond (path ++ [atom]) present
    simp [path] at bounded

/-- Canonical ordinary-double neighbors of one source atom. -/
noncomputable def aromaticCanonicalOrdinaryDoubleNeighbors
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    List source.AromaticCanonicalAtom := by
  classical
  exact source.aromaticCanonicalAtomUniverse.filter fun neighbor =>
    decide (source.AromaticCanonicalOrdinaryDoubleBond atom neighbor)

theorem mem_aromaticCanonicalOrdinaryDoubleNeighbors_iff
    (source : AuthoritativeChemicalInput)
    (atom neighbor : source.AromaticCanonicalAtom) :
    neighbor ∈ source.aromaticCanonicalOrdinaryDoubleNeighbors atom ↔
      source.AromaticCanonicalOrdinaryDoubleBond atom neighbor := by
  classical
  simp [aromaticCanonicalOrdinaryDoubleNeighbors]

/-- Two atoms lie in the same ordinary-double network when one enumerated simple path contains
both.  The exhaustive path enumeration makes this finite and decidable. -/
def AromaticCanonicalOrdinaryDoubleConnected
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) : Prop :=
  ∃ path ∈ source.aromaticCanonicalOrdinaryCumulenePaths,
    left ∈ path ∧ right ∈ path

/-- The connected ordinary-double network containing a bond has a branch vertex. -/
def AromaticCanonicalOrdinaryDoubleBondBranched
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) : Prop :=
  ∃ atom ∈ source.aromaticCanonicalAtomUniverse,
    source.AromaticCanonicalOrdinaryDoubleConnected bond.left atom ∧
      3 ≤ (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length

/-- An enumerated simple ordinary-double cycle contains this bond. -/
def AromaticCanonicalOrdinaryDoubleBondCyclic
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) : Prop :=
  ∃ cycle ∈ source.aromaticCanonicalOrdinaryCumuleneCycles,
    AromaticCanonicalPathContainsBond cycle bond.left bond.right

/-- A chosen exhaustive cycle witness when the bond is cyclic. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondCycle
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    List source.AromaticCanonicalAtom :=
  Classical.choose cyclic

theorem aromaticCanonicalOrdinaryDoubleBondCycle_spec
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    source.aromaticCanonicalOrdinaryDoubleBondCycle bond cyclic ∈
        source.aromaticCanonicalOrdinaryCumuleneCycles ∧
      AromaticCanonicalPathContainsBond
        (source.aromaticCanonicalOrdinaryDoubleBondCycle bond cyclic)
        bond.left bond.right :=
  Classical.choose_spec cyclic

theorem aromaticCanonicalOrdinaryDoubleBondCycle_length_three_le
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    3 ≤ (source.aromaticCanonicalOrdinaryDoubleBondCycle bond cyclic).length := by
  have valid :=
    (source.mem_aromaticCanonicalOrdinaryCumuleneCycles_iff
      (source.aromaticCanonicalOrdinaryDoubleBondCycle bond cyclic)).mp
        (source.aromaticCanonicalOrdinaryDoubleBondCycle_spec bond cyclic).1
  rcases valid with ⟨first, middle, last, identity, length, path, closing⟩
  exact length

/-- Canonical global topology supplied to the independent P-93 routing relation.  Branching has
priority over a cycle embedded in a more complex network; a nonbranched cycle is cyclic; every
remaining connected bond uses its deterministic maximum-length open path. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondTopology
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    BlueBookP93.Acyclic.ConsecutiveDoubleBondTopology := by
  classical
  if branched : source.AromaticCanonicalOrdinaryDoubleBondBranched bond then
    exact .branchedNetwork
  else if cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond then
    let cycle := source.aromaticCanonicalOrdinaryDoubleBondCycle bond cyclic
    exact .closedCycle cycle.length (by
      have length := source.aromaticCanonicalOrdinaryDoubleBondCycle_length_three_le bond cyclic
      exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) length))
  else
    let path := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond
    exact .openChain (path.length - 1) (by
      have length := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_length_two_le bond
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt length))

theorem aromaticCanonicalOrdinaryDoubleBondTopology_eq_branched
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (branched : source.AromaticCanonicalOrdinaryDoubleBondBranched bond) :
    source.aromaticCanonicalOrdinaryDoubleBondTopology bond = .branchedNetwork := by
  simp [aromaticCanonicalOrdinaryDoubleBondTopology, branched]

theorem aromaticCanonicalOrdinaryDoubleBondTopology_eq_closedCycle
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    ∃ count nonempty,
      source.aromaticCanonicalOrdinaryDoubleBondTopology bond =
        .closedCycle count nonempty := by
  let cycle := source.aromaticCanonicalOrdinaryDoubleBondCycle bond cyclic
  have nonempty : cycle.length ≠ 0 := by
    have length := source.aromaticCanonicalOrdinaryDoubleBondCycle_length_three_le bond cyclic
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) length)
  exact ⟨cycle.length, nonempty, by
    simp [aromaticCanonicalOrdinaryDoubleBondTopology, notBranched, cyclic, cycle]⟩

theorem aromaticCanonicalOrdinaryDoubleBondTopology_eq_openChain
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    ∃ count nonempty,
      source.aromaticCanonicalOrdinaryDoubleBondTopology bond =
        .openChain count nonempty := by
  let path := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond
  have nonempty : path.length - 1 ≠ 0 := by
    have length := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_length_two_le bond
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt length)
  exact ⟨path.length - 1, nonempty, by
    simp [aromaticCanonicalOrdinaryDoubleBondTopology, notBranched, notCyclic, path]⟩

/-- In the open case, the independent topology carries exactly the edge count of the chosen
maximum source path. -/
theorem aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    ∃ nonempty :
        (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 0,
      source.aromaticCanonicalOrdinaryDoubleBondTopology bond =
        .openChain
          ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1)
          nonempty := by
  let path := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond
  have nonempty : path.length - 1 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_length_two_le bond))
  exact ⟨nonempty, by
    simp [aromaticCanonicalOrdinaryDoubleBondTopology,
      notBranched, notCyclic]⟩

/-- The unique independent P-93 owner route for one canonical source bond. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondRoute
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute :=
  Classical.choose
    (BlueBookP93.Acyclic.existsUnique_doubleBondAnalysisRoute
      (source.aromaticCanonicalOrdinaryDoubleBondTopology bond))

theorem aromaticCanonicalOrdinaryDoubleBondRoute_applies
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    BlueBookP93.Acyclic.DoubleBondAnalysisRouteApplies
      (source.aromaticCanonicalOrdinaryDoubleBondTopology bond)
      (source.aromaticCanonicalOrdinaryDoubleBondRoute bond) :=
  (Classical.choose_spec
    (BlueBookP93.Acyclic.existsUnique_doubleBondAnalysisRoute
      (source.aromaticCanonicalOrdinaryDoubleBondTopology bond))).1

theorem aromaticCanonicalOrdinaryDoubleBondRoute_unique
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (applies : BlueBookP93.Acyclic.DoubleBondAnalysisRouteApplies
      (source.aromaticCanonicalOrdinaryDoubleBondTopology bond) route) :
    route = source.aromaticCanonicalOrdinaryDoubleBondRoute bond := by
  exact (Classical.choose_spec
    (BlueBookP93.Acyclic.existsUnique_doubleBondAnalysisRoute
      (source.aromaticCanonicalOrdinaryDoubleBondTopology bond))).2 route applies

/-- Every canonical source bond whose unique owner is the requested P-93 route. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute) :
    List source.AromaticCanonicalOrdinaryDoubleBondCarrier := by
  classical
  exact source.aromaticCanonicalOrdinaryDoubleBondPairs.attach.filter fun bond =>
    decide (source.aromaticCanonicalOrdinaryDoubleBondRoute bond = route)

@[simp] theorem mem_aromaticCanonicalOrdinaryDoubleBondRouteCarriers_iff
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers route ↔
      source.aromaticCanonicalOrdinaryDoubleBondRoute bond = route := by
  classical
  simp [aromaticCanonicalOrdinaryDoubleBondRouteCarriers]

theorem aromaticCanonicalOrdinaryDoubleBondRouteCarriers_nodup
    (source : AuthoritativeChemicalInput)
    (route : BlueBookP93.Acyclic.DoubleBondAnalysisRoute) :
    (source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers route).Nodup := by
  classical
  exact source.aromaticCanonicalOrdinaryDoubleBondPairs_nodup.attach.filter _

/-- Exhaustive and exclusive ownership: every canonical physical ordinary-double bond occurs in
exactly one route carrier. -/
theorem existsUnique_mem_aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    ∃! route, bond ∈ source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers route := by
  refine ⟨source.aromaticCanonicalOrdinaryDoubleBondRoute bond, by simp, ?_⟩
  intro route present
  exact (source.mem_aromaticCanonicalOrdinaryDoubleBondRouteCarriers_iff
    route bond).mp present |>.symm

theorem aromaticCanonicalOrdinaryDoubleBondRouteCarriers_disjoint
    (source : AuthoritativeChemicalInput)
    {leftRoute rightRoute : BlueBookP93.Acyclic.DoubleBondAnalysisRoute}
    (different : leftRoute ≠ rightRoute) :
    List.Disjoint
      (source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers leftRoute)
      (source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers rightRoute) := by
  rw [List.disjoint_left]
  intro bond leftPresent rightPresent
  have leftIdentity :=
    (source.mem_aromaticCanonicalOrdinaryDoubleBondRouteCarriers_iff
      leftRoute bond).mp leftPresent
  have rightIdentity :=
    (source.mem_aromaticCanonicalOrdinaryDoubleBondRouteCarriers_iff
      rightRoute bond).mp rightPresent
  exact different (leftIdentity.symm.trans rightIdentity)

/-- Canonical source bonds owned as ordinary individual double-bond units. -/
noncomputable def aromaticCanonicalIndividualDoubleBondCarriers
    (source : AuthoritativeChemicalInput) :=
  source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute.individualDoubleBond

/-- Canonical source bonds owned by planar odd-open-cumulene analysis. -/
noncomputable def aromaticCanonicalOddOpenCumuleneBondCarriers
    (source : AuthoritativeChemicalInput) :=
  source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute.oddOpenCumulene

/-- Canonical source bonds owned by axial even-open-cumulene analysis. -/
noncomputable def aromaticCanonicalEvenOpenCumuleneBondCarriers
    (source : AuthoritativeChemicalInput) :=
  source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute.evenOpenCumulene

/-- Canonical source bonds owned by fully cyclic-cumulene perception. -/
noncomputable def aromaticCanonicalCyclicCumuleneBondCarriers
    (source : AuthoritativeChemicalInput) :=
  source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute.cyclicCumulenePerception

/-- Canonical source bonds individually exposed from a branched order-two network. -/
noncomputable def aromaticCanonicalBranchedPerBondCarriers
    (source : AuthoritativeChemicalInput) :=
  source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers
    BlueBookP93.Acyclic.DoubleBondAnalysisRoute.eachBondOfBranchedNetwork

/-- The five named ownership lists exhaust every canonical source ordinary-double bond. -/
theorem mem_one_of_aromaticCanonicalDoubleBondOwnerCarriers
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ∨
      bond ∈ source.aromaticCanonicalOddOpenCumuleneBondCarriers ∨
      bond ∈ source.aromaticCanonicalEvenOpenCumuleneBondCarriers ∨
      bond ∈ source.aromaticCanonicalCyclicCumuleneBondCarriers ∨
      bond ∈ source.aromaticCanonicalBranchedPerBondCarriers := by
  cases routeIdentity : source.aromaticCanonicalOrdinaryDoubleBondRoute bond <;>
    simp [aromaticCanonicalIndividualDoubleBondCarriers,
      aromaticCanonicalOddOpenCumuleneBondCarriers,
      aromaticCanonicalEvenOpenCumuleneBondCarriers,
      aromaticCanonicalCyclicCumuleneBondCarriers,
      aromaticCanonicalBranchedPerBondCarriers, routeIdentity]

/-- No canonical bond can occur in two different named owner lists. -/
theorem not_mem_two_aromaticCanonicalDoubleBondOwnerCarriers
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftRoute rightRoute : BlueBookP93.Acyclic.DoubleBondAnalysisRoute)
    (different : leftRoute ≠ rightRoute)
    (leftPresent : bond ∈
      source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers leftRoute) :
    bond ∉ source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers rightRoute := by
  intro rightPresent
  exact (source.aromaticCanonicalOrdinaryDoubleBondRouteCarriers_disjoint different)
    leftPresent rightPresent

/-- Branch detection forces the independent per-bond route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (branched : source.AromaticCanonicalOrdinaryDoubleBondBranched bond) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond =
      .eachBondOfBranchedNetwork := by
  apply Eq.symm
  apply source.aromaticCanonicalOrdinaryDoubleBondRoute_unique bond
  rw [source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_branched bond branched]
  trivial

/-- A nonbranched cycle forces the independent cyclic-cumulene route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond =
      .cyclicCumulenePerception := by
  obtain ⟨count, nonempty, topology⟩ :=
    source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_closedCycle
      bond notBranched cyclic
  apply Eq.symm
  apply source.aromaticCanonicalOrdinaryDoubleBondRoute_unique bond
  rw [topology]
  trivial

/-- A nonbranched, noncyclic one-edge maximum path is an ordinary individual double bond. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_individual
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond)
    (ordinary :
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 = 1) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .individualDoubleBond := by
  let path := source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond
  have nonempty : path.length - 1 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath_length_two_le bond))
  have topology : source.aromaticCanonicalOrdinaryDoubleBondTopology bond =
      .openChain (path.length - 1) nonempty := by
    simp [aromaticCanonicalOrdinaryDoubleBondTopology,
      notBranched, notCyclic, path]
  apply Eq.symm
  apply source.aromaticCanonicalOrdinaryDoubleBondRoute_unique bond
  rw [topology]
  change path.length - 1 = 1
  simpa [path] using ordinary

/-- A nonbranched, noncyclic longer odd-edge path uses the planar odd-cumulene route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_oddOpen
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond)
    (notOrdinary :
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 1)
    (odd : Odd
      ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1)) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .oddOpenCumulene := by
  obtain ⟨nonempty, topology⟩ :=
    source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
      bond notBranched notCyclic
  apply Eq.symm
  apply source.aromaticCanonicalOrdinaryDoubleBondRoute_unique bond
  rw [topology]
  exact ⟨notOrdinary, odd⟩

/-- A nonbranched, noncyclic longer even-edge path uses the axial even-cumulene route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_evenOpen
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond)
    (notOrdinary :
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 1)
    (notOdd : ¬Odd
      ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1)) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .evenOpenCumulene := by
  obtain ⟨nonempty, topology⟩ :=
    source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
      bond notBranched notCyclic
  apply Eq.symm
  apply source.aromaticCanonicalOrdinaryDoubleBondRoute_unique bond
  rw [topology]
  exact ⟨notOrdinary, notOdd⟩

/-- Exact independent meaning of the individual-double-bond route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_individual_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .individualDoubleBond ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond ∧
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 = 1 := by
  constructor
  · intro routeIdentity
    have notBranched :
        ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
      intro branched
      have branchIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond bond branched
      cases routeIdentity.symm.trans branchIdentity
    have notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond := by
      intro cyclic
      have cyclicIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic
          bond notBranched cyclic
      cases routeIdentity.symm.trans cyclicIdentity
    obtain ⟨nonempty, topology⟩ :=
      source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
        bond notBranched notCyclic
    have applies := source.aromaticCanonicalOrdinaryDoubleBondRoute_applies bond
    rw [topology, routeIdentity] at applies
    exact ⟨notBranched, notCyclic, applies⟩
  · rintro ⟨notBranched, notCyclic, ordinary⟩
    exact source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_individual
      bond notBranched notCyclic ordinary

/-- Exact independent meaning of the planar odd-open-cumulene route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_oddOpen_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .oddOpenCumulene ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond ∧
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 1 ∧
      Odd ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1) := by
  constructor
  · intro routeIdentity
    have notBranched :
        ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
      intro branched
      have branchIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond bond branched
      cases routeIdentity.symm.trans branchIdentity
    have notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond := by
      intro cyclic
      have cyclicIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic
          bond notBranched cyclic
      cases routeIdentity.symm.trans cyclicIdentity
    obtain ⟨nonempty, topology⟩ :=
      source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
        bond notBranched notCyclic
    have applies := source.aromaticCanonicalOrdinaryDoubleBondRoute_applies bond
    rw [topology, routeIdentity] at applies
    exact ⟨notBranched, notCyclic, applies.1, applies.2⟩
  · rintro ⟨notBranched, notCyclic, notOrdinary, odd⟩
    exact source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_oddOpen
      bond notBranched notCyclic notOrdinary odd

/-- Exact independent meaning of the axial even-open-cumulene route. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_evenOpen_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .evenOpenCumulene ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond ∧
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 1 ∧
      ¬Odd ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1) := by
  constructor
  · intro routeIdentity
    have notBranched :
        ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
      intro branched
      have branchIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond bond branched
      cases routeIdentity.symm.trans branchIdentity
    have notCyclic : ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond := by
      intro cyclic
      have cyclicIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic
          bond notBranched cyclic
      cases routeIdentity.symm.trans cyclicIdentity
    obtain ⟨nonempty, topology⟩ :=
      source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
        bond notBranched notCyclic
    have applies := source.aromaticCanonicalOrdinaryDoubleBondRoute_applies bond
    rw [topology, routeIdentity] at applies
    exact ⟨notBranched, notCyclic, applies.1, applies.2⟩
  · rintro ⟨notBranched, notCyclic, notOrdinary, notOdd⟩
    exact source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_evenOpen
      bond notBranched notCyclic notOrdinary notOdd

/-- Exact independent meaning of cyclic-cumulene ownership. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .cyclicCumulenePerception ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      source.AromaticCanonicalOrdinaryDoubleBondCyclic bond := by
  constructor
  · intro routeIdentity
    have notBranched :
        ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
      intro branched
      have branchIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond bond branched
      cases routeIdentity.symm.trans branchIdentity
    refine ⟨notBranched, ?_⟩
    by_contra notCyclic
    obtain ⟨nonempty, topology⟩ :=
      source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
        bond notBranched notCyclic
    have applies := source.aromaticCanonicalOrdinaryDoubleBondRoute_applies bond
    rw [topology, routeIdentity] at applies
    exact applies.elim
  · rintro ⟨notBranched, cyclic⟩
    exact source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic
      bond notBranched cyclic

/-- Exact independent meaning of per-bond ownership in a branched order-two network. -/
theorem aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    source.aromaticCanonicalOrdinaryDoubleBondRoute bond = .eachBondOfBranchedNetwork ↔
      source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
  constructor
  · intro routeIdentity
    by_contra notBranched
    by_cases cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond
    · have cyclicIdentity :=
        source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic
          bond notBranched cyclic
      cases routeIdentity.symm.trans cyclicIdentity
    · obtain ⟨nonempty, topology⟩ :=
        source.aromaticCanonicalOrdinaryDoubleBondTopology_eq_canonicalOpenChain
          bond notBranched cyclic
      have applies := source.aromaticCanonicalOrdinaryDoubleBondRoute_applies bond
      rw [topology, routeIdentity] at applies
      exact applies.elim
  · exact source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond bond

@[simp] theorem mem_aromaticCanonicalIndividualDoubleBondCarriers_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond ∧
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 = 1 := by
  simpa [aromaticCanonicalIndividualDoubleBondCarriers] using
    source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_individual_iff bond

@[simp] theorem mem_aromaticCanonicalOddOpenCumuleneBondCarriers_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalOddOpenCumuleneBondCarriers ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond ∧
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 1 ∧
      Odd ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1) := by
  simpa [aromaticCanonicalOddOpenCumuleneBondCarriers] using
    source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_oddOpen_iff bond

@[simp] theorem mem_aromaticCanonicalEvenOpenCumuleneBondCarriers_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalEvenOpenCumuleneBondCarriers ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      ¬ source.AromaticCanonicalOrdinaryDoubleBondCyclic bond ∧
      (source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1 ≠ 1 ∧
      ¬Odd ((source.aromaticCanonicalOrdinaryDoubleBondCanonicalPath bond).length - 1) := by
  simpa [aromaticCanonicalEvenOpenCumuleneBondCarriers] using
    source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_evenOpen_iff bond

@[simp] theorem mem_aromaticCanonicalCyclicCumuleneBondCarriers_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalCyclicCumuleneBondCarriers ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      source.AromaticCanonicalOrdinaryDoubleBondCyclic bond := by
  simpa [aromaticCanonicalCyclicCumuleneBondCarriers] using
    source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_cyclic_iff bond

@[simp] theorem mem_aromaticCanonicalBranchedPerBondCarriers_iff
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalBranchedPerBondCarriers ↔
      source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
  simpa [aromaticCanonicalBranchedPerBondCarriers] using
    source.aromaticCanonicalOrdinaryDoubleBondRoute_eq_branchedPerBond_iff bond

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
