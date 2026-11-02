import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# A node/key witness for context-depth Rule 1b divergence

This small witness isolates the history-sensitive observation that blocks a raw fresh-root
transport for auxiliary occurrences.  The original context starts at atom `1`, visits target `0`,
and then has an outward real node at atom `2`.  Their stored real-node Rule-1b distances are `0`
and `2`.  Fresh ligand roots `rootFromEdge 0 1` and `rootFromEdge 0 2` both have Rule-1b distance
`1`.

The explicit rule-major keys have the same Rule-1a data.  With equal Rule-2 data, context depth
alone makes the parent arm strictly outrank the outward arm; after fresh rooting, they tie.  With
Rule-2 masses `12` and `13`, context depth makes the `12` arm win, while fresh rooting ties Rule 1b
and lets Rule 2 put the `13` arm first in the fresh-root comparison. This is a kernel-checked
node/key witness; it does not claim a complete admitted molecular input or an actual builder
trace. The disagreement does not by itself identify a chemical error: the accepted auxiliary
profile retains the outer digraph, while final descriptors use a fresh centre-rooted digraph.
-/

namespace TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness

open TetraStereo.OneCenter

abbrev Atom := Nat

def originalContextRoot : OfficialCIPNode Atom := OfficialCIPNode.root 1

def auxiliaryTarget : OfficialCIPNode Atom := originalContextRoot.extend 0 0

def auxiliaryOutwardNode : OfficialCIPNode Atom := auxiliaryTarget.extend 2 0

def freshParentLigandRoot : OfficialCIPNode Atom := OfficialCIPNode.rootFromEdge 0 1

def freshOutwardLigandRoot : OfficialCIPNode Atom := OfficialCIPNode.rootFromEdge 0 2

theorem actualHistoryDistances :
    originalContextRoot.rule1bRootDistance = 0 ∧
      auxiliaryOutwardNode.rule1bRootDistance = 2 := by
  decide +kernel

theorem freshLigandRootDistances :
    freshParentLigandRoot.rule1bRootDistance = 1 ∧
      freshOutwardLigandRoot.rule1bRootDistance = 1 := by
  decide +kernel

private def keyAt (node : OfficialCIPNode Atom) (isotopeMass : Nat) :
    OfficialRuleMajorKey Atom :=
  { rule1a := [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]]
    rule1b := [[([], node.rule1bRootDistance)]]
    rule2 := [[([], isotopeMass)]]
    sourceNodes := []
    complete := true }

theorem sameRule1aData :
    (keyAt originalContextRoot 12).rule1a = (keyAt auxiliaryOutwardNode 13).rule1a := rfl

theorem contextDepthAloneBreaksNeutralTie :
    OfficialRuleMajorKey.compare (keyAt originalContextRoot 12)
        (keyAt auxiliaryOutwardNode 12) = Ordering.gt ∧
      OfficialRuleMajorKey.compare (keyAt freshParentLigandRoot 12)
        (keyAt freshOutwardLigandRoot 12) = Ordering.eq := by
  decide +kernel

theorem contextDepthReversesIsotopeDecision :
    OfficialRuleMajorKey.compare (keyAt originalContextRoot 12)
        (keyAt auxiliaryOutwardNode 13) = Ordering.gt ∧
      OfficialRuleMajorKey.compare (keyAt freshParentLigandRoot 12)
        (keyAt freshOutwardLigandRoot 13) = Ordering.lt := by
  decide +kernel

end TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness.actualHistoryDistances
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness.freshLigandRootDistances
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness.sameRule1aData
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness.contextDepthAloneBreaksNeutralTie
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRerootContextRule1bWitness.contextDepthReversesIsotopeDecision
