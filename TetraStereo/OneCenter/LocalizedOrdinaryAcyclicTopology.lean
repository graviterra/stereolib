import TetraStereo.OneCenter.LocalizedFamilyAssignmentsExecutable
import TetraStereo.OneCenter.FiniteGraphReachabilityExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OrdinaryPlanar

/-- The complete positive-bond graph with this one physical edge removed. -/
def cutGraph (input : CertifiedLocalizedCIPInput) (bond : input.LocalizedCanonicalDoubleBond) :
    SimpleGraph input.Atom :=
  input.moleculeGraph.underlyingSimpleGraph \ SimpleGraph.fromEdgeSet {s(bond.1.1, bond.1.2)}

instance cutGraphAdjDecidable (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) : DecidableRel (cutGraph input bond).Adj := by
  unfold cutGraph
  infer_instance

/-- Both family ownership and physical acyclicity are retained. Rings elsewhere in the molecule
are permitted; a ring containing this double bond is excluded. -/
structure Topology (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) where
  axis : input.LocalizedRule3CumulatedEndpointCursorFrame fuel
  axisMeaning : input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
    (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) axis
  ordinary : axis.doubleBondCount = 1
  leftExact : axis.initial.left = bond.1.1
  rightExact : axis.right = bond.1.2
  bridge : input.moleculeGraph.underlyingSimpleGraph.IsBridge s(bond.1.1, bond.1.2)

/-- Bounded finite reachability constructs the bridge proof; no molecular proof is supplied by
the caller. Complete one-edge axis perception distinguishes ordinary bonds from cumulenes. -/
def topology? (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) : Option (Topology input fuel bond) :=
  letI := FiniteGraphReachability.reachableDecidable (cutGraph input bond) bond.1.1 bond.1.2
  if disconnected : ¬ (cutGraph input bond).Reachable bond.1.1 bond.1.2 then
    let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond
    match computed : input.localizedRule3CumulatedEndpointCursorFrameExec?
        (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
    | none => none
    | some axis =>
        if ordinary : axis.doubleBondCount = 1 then
          if leftExact : axis.initial.left = bond.1.1 then
            if rightExact : axis.right = bond.1.2 then some
              { axis, ordinary, leftExact, rightExact
                axisMeaning := by
                  have sound := input.localizedRule3CumulatedEndpointCursorFrame?_sound
                    (input.localizedRule3CumulatedTraversalFuel fuel) occurrence axis
                    ((input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_original
                      _ occurrence).symm.trans computed)
                  simpa only [occurrence,
                    input.localizedCanonicalDoubleBondFirstChildOccurrenceExec_eq] using sound
                bridge := by
                  apply SimpleGraph.isBridge_iff.mpr
                  refine ⟨?_, disconnected⟩
                  have edge := ((input.mem_localizedCanonicalDoubleBondPairs_iff
                    bond.1.1 bond.1.2).mp bond.2).2
                  change 0 < input.moleculeGraph.bond bond.1.1 bond.1.2
                  rw [edge]
                  decide }
            else none
          else none
        else none
  else none

theorem topology?_none_of_reachable (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (connected : (cutGraph input bond).Reachable bond.1.1 bond.1.2) :
    topology? input fuel bond = none := by
  simp [topology?, connected]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OrdinaryPlanar
