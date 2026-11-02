import TetraStereo.OneCenter.P93MolecularFullereneSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Explicit locant involutions on fullerene carriers

Concrete improper symmetries in the P-93 examples are most compactly represented by their
locant image table.  The certificate below asks only that the table stays in the carrier and is
an involution.  Those two small source-data facts construct the full proof-carrying permutation;
no inverse search or global injectivity normalization is involved.
-/

namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

structure MolecularFullereneLocantInvolutionCertificate
    (input : MolecularFullereneConfigurationInput) where
  table : List Nat
  mapsCarrier : ∀ atom ∈ input.carrier, table.getD atom atom ∈ input.carrier
  involutive : ∀ atom ∈ input.carrier,
    table.getD (table.getD atom atom) (table.getD atom atom) = atom

namespace MolecularFullereneLocantInvolutionCertificate

def toPerm {input : MolecularFullereneConfigurationInput}
    (certificate : MolecularFullereneLocantInvolutionCertificate input) :
    Equiv.Perm (MolecularFullereneCarrierAtom input) where
  toFun atom := ⟨certificate.table.getD atom.1 atom.1,
    certificate.mapsCarrier atom.1 atom.2⟩
  invFun atom := ⟨certificate.table.getD atom.1 atom.1,
    certificate.mapsCarrier atom.1 atom.2⟩
  left_inv atom := by
    apply Subtype.ext
    exact certificate.involutive atom.1 atom.2
  right_inv atom := by
    apply Subtype.ext
    exact certificate.involutive atom.1 atom.2

@[simp] theorem toPerm_apply_val {input : MolecularFullereneConfigurationInput}
    (certificate : MolecularFullereneLocantInvolutionCertificate input)
    (atom : MolecularFullereneCarrierAtom input) :
    (certificate.toPerm atom).1 = certificate.table.getD atom.1 atom.1 := rfl

@[simp] theorem toPerm_involutive {input : MolecularFullereneConfigurationInput}
    (certificate : MolecularFullereneLocantInvolutionCertificate input)
    (atom : MolecularFullereneCarrierAtom input) :
    certificate.toPerm (certificate.toPerm atom) = atom := by
  apply Subtype.ext
  exact certificate.involutive atom.1 atom.2

end MolecularFullereneLocantInvolutionCertificate

/-- For an involution, one-way preservation of positive cage bonds automatically gives the
reverse implication and hence the complete carrier-automorphism judgment. -/
theorem molecularFullereneCarrierAutomorphism_of_involutive_forward
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (involutive : ∀ atom, symmetry (symmetry atom) = atom)
    (forward : ∀ left right : MolecularFullereneCarrierAtom input,
      0 < molecule.bondOrder left.1 right.1 →
        0 < molecule.bondOrder (symmetry left).1 (symmetry right).1) :
    MolecularFullereneCarrierAutomorphism molecule input symmetry := by
  intro left right
  constructor
  · exact forward left right
  · intro mappedBond
    have twice := forward (symmetry left) (symmetry right) mappedBond
    simpa only [involutive] using twice

end TetraStereo.OneCenter.BlueBookP93.Cyclic

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneLocantInvolutionCertificate.toPerm
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneCarrierAutomorphism_of_involutive_forward
