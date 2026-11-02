import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedAnalysis

set_option autoImplicit false

/-!
# Source-independent carrier for canonical Rules 4b/5 transport

This small module removes the source-dependent center type from the public observation surface.
The exact executable-to-builder-free-complete mathematics lives in
`IUPACRule45CanonicalPartitionCompleteness`; obsolete conditional reverse-transport scaffolding is
deliberately absent here.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Source-independent observation carrier for the canonical Rules 4b/5 fixed-point endpoint.
The dependent proof that `centerAtom` is a perceived tetrahedral center belongs to the judgment,
not to this public observation type. -/
structure Rule45CanonicalProvisionObservation where
  carrierFuel : Nat
  ruleFuel : Nat
  centerAtom : Nat
  descriptor : RS
  deriving DecidableEq, Repr

/-- Fixed production meaning: the actual concrete source evaluator emits this descriptor for the
perceived center at `centerAtom`. -/
def Rule45CanonicalProvisionProductionJudged
    (source : AuthoritativeChemicalInput)
    (observation : Rule45CanonicalProvisionObservation) : Prop :=
  ∃ center : source.AromaticCanonicalTetrahedralCenter,
    center.1.val = observation.centerAtom ∧
      source.aromaticCanonicalConcreteRule3Through6Descriptor?
          observation.carrierFuel observation.ruleFuel center = some observation.descriptor

end IUPACNormativeProvision
end TetraStereo.OneCenter
