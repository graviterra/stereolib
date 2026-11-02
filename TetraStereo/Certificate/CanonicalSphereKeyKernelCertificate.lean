import TetraStereo.Certificate.CanonicalSphereKey
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace Certificate
namespace CanonicalSphereKey
namespace KernelCertificate

/-! Concrete atomic-number trees, three dense slots per node, spheres `0, …, 3`.  These are
illustrations of the generic order; they do not assert the IUPAC reading of P-92. -/

private def leaf (z : ℕ) : HTree ℕ := .node z []

/-- `C(-CH2Br)(H)(H)`: the heavy atom is two spheres from the ligand atom. -/
private def bromoethyl : HTree ℕ :=
  .node 6 [.node 6 [leaf 35, leaf 1, leaf 1], leaf 1, leaf 1]

/-- `C(-OH)(H)(H)`: oxygen is one sphere from the ligand atom. -/
private def hydroxymethyl : HTree ℕ :=
  .node 6 [.node 8 [leaf 1], leaf 1, leaf 1]

/-- `C(-CH2Cl)(H)(H)`: a depth-first key ranks this above `dimethyl`. -/
private def chloroethyl : HTree ℕ :=
  .node 6 [.node 6 [leaf 17, leaf 1, leaf 1], leaf 1, leaf 1]

/-- `C(-CH3)(-CH3)(H)`: sphere one is `{C, C, H}` against `{C, H, H}`. -/
private def dimethyl : HTree ℕ :=
  .node 6 [.node 6 [leaf 1, leaf 1, leaf 1], .node 6 [leaf 1, leaf 1, leaf 1], leaf 1]

/-- A nearer heteroatom outranks a heavier deeper atom. -/
theorem nearer_oxygen_outranks_deeper_bromine : Higher 3 3 hydroxymethyl bromoethyl := by
  decide

/-- Sphere-major order: the first differing sphere decides, not the first differing branch. -/
theorem sphere_major_not_depth_first : Higher 3 3 dimethyl chloroethyl := by
  decide

/-- Listing order of siblings is not observed. -/
theorem sibling_listing_order_tied :
    Tied 3 3 (.node 6 [leaf 1, leaf 8, leaf 1]) (.node 6 [leaf 8, leaf 1, leaf 1]) := by
  decide

end KernelCertificate
end CanonicalSphereKey
end Certificate
end TetraStereo

assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.ckey_perm
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.ckey_congr
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.ckey_wellShaped
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.ckey_eq_iff_observation
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.ckey_lt_iff_first_difference
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.higher_trans
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.higher_trichotomous
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.tied_observation
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.orderedKey_eq_ckey
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.ckey_canonicalize
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.canonicalize_canonicallyOrdered
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.orderedKey_canonicalize
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.slotOf_lt_slotOf_iff
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.keyObservation_orderedKey_eq_labelAt
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.observation_eq_labelAt
assert_kernel_only TetraStereo.Certificate.CanonicalSphereKey.observation_eq_labelAt_canonicalize
assert_kernel_only
  TetraStereo.Certificate.CanonicalSphereKey.KernelCertificate.nearer_oxygen_outranks_deeper_bromine
assert_kernel_only
  TetraStereo.Certificate.CanonicalSphereKey.KernelCertificate.sphere_major_not_depth_first
assert_kernel_only
  TetraStereo.Certificate.CanonicalSphereKey.KernelCertificate.sibling_listing_order_tied
