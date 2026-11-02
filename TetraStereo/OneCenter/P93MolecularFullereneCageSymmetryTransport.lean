import TetraStereo.OneCenter.P93MolecularFullereneCertificateTransport
import TetraStereo.OneCenter.P93MolecularFullereneAutomorphismCertificate
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Transport of complete fullerene symmetry corpora

Appending addends changes no bond order inside the certified cage carrier.  Consequently the
complete finite corpus of orientation-reversing cage automorphisms is identical for the parent
core and every compiled derivative.  This prevents all five derivative audits from regenerating
or re-enumerating the parent-cage symmetry group.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

theorem MolecularFullereneCageAgreement.carrierAutomorphism_iff
    {reference derivative : RawMolecule}
    {input : MolecularFullereneConfigurationInput}
    (agreement : MolecularFullereneCageAgreement reference derivative input.carrier)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    MolecularFullereneCarrierAutomorphism reference input symmetry ↔
      MolecularFullereneCarrierAutomorphism derivative input symmetry := by
  constructor <;> intro automorphism left right
  · rw [agreement.bondOrder left.1 left.2 right.1 right.2,
      agreement.bondOrder (symmetry left).1 (symmetry left).2
        (symmetry right).1 (symmetry right).2]
    exact automorphism left right
  · rw [← agreement.bondOrder left.1 left.2 right.1 right.2,
      ← agreement.bondOrder (symmetry left).1 (symmetry left).2
        (symmetry right).1 (symmetry right).2]
    exact automorphism left right

/-- Colored-cage chirality is invariant under exact induced-cage agreement once both molecules
carry the audited oriented face map.  This is the mathematical transport used by every compiled
derivative: external atoms and attachment bonds cannot change any parent-cage symmetry result. -/
theorem MolecularFullereneCageAgreement.coloringChiral_iff
    {reference derivative : RawMolecule}
    {input : MolecularFullereneConfigurationInput}
    (agreement : MolecularFullereneCageAgreement reference derivative input.carrier)
    (referenceOriented : OrientedMolecularFullereneFaceMapJudgment reference input)
    (derivativeOriented : OrientedMolecularFullereneFaceMapJudgment derivative input)
    (color : Nat → Nat) :
    MolecularFullereneColoringChiral reference input color ↔
      MolecularFullereneColoringChiral derivative input color := by
  constructor
  · rintro ⟨_oriented, noReversing⟩
    refine ⟨derivativeOriented, ?_⟩
    rintro ⟨symmetry, automorphism, reversing, preserved⟩
    exact noReversing ⟨symmetry,
      (agreement.carrierAutomorphism_iff symmetry).2 automorphism,
      reversing, preserved⟩
  · rintro ⟨_oriented, noReversing⟩
    refine ⟨referenceOriented, ?_⟩
    rintro ⟨symmetry, automorphism, reversing, preserved⟩
    exact noReversing ⟨symmetry,
      (agreement.carrierAutomorphism_iff symmetry).1 automorphism,
      reversing, preserved⟩
/-- A complete reversing corpus transports unchanged across exact induced-cage agreement. -/
def MolecularFullereneCageAgreement.transportReversingCertificate
    {reference derivative : RawMolecule}
    {input : MolecularFullereneConfigurationInput}
    (agreement : MolecularFullereneCageAgreement reference derivative input.carrier)
    (certificate : MolecularFullereneReversingAutomorphismCertificate reference input) :
    MolecularFullereneReversingAutomorphismCertificate derivative input where
  members := certificate.members
  sound := by
    intro symmetry present
    have certified := certificate.sound symmetry present
    exact ⟨(agreement.carrierAutomorphism_iff symmetry).1 certified.1, certified.2⟩
  complete := by
    intro symmetry automorphism reversing
    exact certificate.complete symmetry
      ((agreement.carrierAutomorphism_iff symmetry).2 automorphism) reversing

end
end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneCageAgreement.carrierAutomorphism_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneCageAgreement.coloringChiral_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneCageAgreement.transportReversingCertificate
