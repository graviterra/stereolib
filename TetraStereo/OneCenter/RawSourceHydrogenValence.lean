import TetraStereo.OneCenter.RawSourceHydrogenPolicy
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# Valence preservation under source hydrogen freezing

`freezeSourceHydrogenCounts` replaces each atom's implicit/inline hydrogen policy with the exact
source count `mol.hydrogenCountAt index`, leaving the atom inventory, every bond, and every other
field untouched.  This module proves that the frozen molecule still satisfies the permissive
validation table `ValenceOK` whenever the source molecule did.

The argument is a direct application of the source-hydrogen support bound
`incidentBondOrderSum_add_hydrogenCountAt_supported`, which already covers bracket atoms with an
exact count, unbracketed atoms filled to their default valence, and the no-fill fallback.  Two
facts about the frozen molecule supply the rest:

* `AtomSpec.allowedValences` ignores `explicitHydrogens?`, so replacing the policy does not change
  the table membership of the witness valence.
* At a real atom the frozen `usedValenceAt` is exactly
  `mol.hydrogenCountAt index + mol.incidentBondOrderSum index`, while the bond list (and hence the
  incident sum) is unchanged.

No P-93 or downstream normalization module is imported; this is the low-dependency production
interface for the freezing step. -/

/-- Replacing only the stored explicit-hydrogen policy leaves the atom's allowed-valence table
intact: the table reads element, charge and aromaticity, never the hydrogen policy. -/
@[simp] theorem allowedValences_replace_explicitHydrogens (atom : AtomSpec) (count : Option Nat) :
    ({ atom with explicitHydrogens? := count } : AtomSpec).allowedValences =
      atom.allowedValences := by
  simp [AtomSpec.allowedValences]

/-- Exact frozen atom lookup at a real source atom, together with the two facts used by the
valence proof: the frozen atom's policy is the source hydrogen count, its allowed-valence table is
the source table, and its used valence is the source hydrogen count plus the unchanged source
incident bond-order sum. -/
theorem freezeSourceHydrogenCounts_atomAt?_valence (mol : RawMolecule) (index : Nat)
    (atom : AtomSpec) (lookup : mol.atomAt? index = some atom) :
    ∃ frozenAtom,
      (freezeSourceHydrogenCounts mol).atomAt? index = some frozenAtom ∧
      frozenAtom.explicitHydrogens? = some (mol.hydrogenCountAt index) ∧
      frozenAtom.allowedValences = atom.allowedValences ∧
      (freezeSourceHydrogenCounts mol).usedValenceAt index =
        mol.hydrogenCountAt index + mol.incidentBondOrderSum index := by
  refine ⟨{ atom with explicitHydrogens? := some (mol.hydrogenCountAt index) }, ?_, rfl, ?_, ?_⟩
  · exact freezeSourceHydrogenCounts_atomAt?_spec mol index atom lookup
  · exact allowedValences_replace_explicitHydrogens atom _
  · exact freezeSourceHydrogenCounts_usedValenceAt_eq mol index atom lookup

/-- Freezing source hydrogen counts preserves the permissive valence contract.  The source count
is exactly the count the existing supported-hydrogen bound was proved for, and freezing copies it
without touching any bond order. -/
theorem freezeSourceHydrogenCounts_valenceOK (mol : RawMolecule) (valid : mol.ValenceOK) :
    (mol.freezeSourceHydrogenCounts).ValenceOK := by
  intro index atom frozenLookup
  cases lookup : mol.atomAt? index with
  | none =>
      have frozenNone : (mol.freezeSourceHydrogenCounts).atomAt? index = none := by
        rw [freezeSourceHydrogenCounts_atomAt?, lookup]
        rfl
      rw [frozenNone] at frozenLookup
      cases frozenLookup
  | some source =>
      have atomIdentity : atom =
          { source with explicitHydrogens? := some (mol.hydrogenCountAt index) } := by
        have frozenSpec := freezeSourceHydrogenCounts_atomAt?_spec mol index source lookup
        rw [frozenSpec] at frozenLookup
        exact (Option.some.inj frozenLookup).symm
      subst atom
      obtain ⟨allowed, allowedMember, supported⟩ :=
        incidentBondOrderSum_add_hydrogenCountAt_supported mol valid index source lookup
      refine ⟨allowed, ?_, ?_⟩
      · simpa using allowedMember
      · rw [freezeSourceHydrogenCounts_usedValenceAt_eq mol index source lookup]
        omega

assert_kernel_only allowedValences_replace_explicitHydrogens
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_valence
assert_kernel_only freezeSourceHydrogenCounts_valenceOK

end RawMolecule
end OneCenter
end TetraStereo
