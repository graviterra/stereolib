import TetraStereo.OneCenter.P93MolecularFullereneCertificateTransport

set_option autoImplicit false

/-!
# Appending derivatives to a certified fullerene cage

A printed fullerene derivative adds atoms and bonds to an already certified numbered cage.  This
module makes that construction literal.  The only graph-separation hypothesis is that no appended
bond has both endpoints in the cage carrier.  Hence addend--addend and cage--addend bonds are
allowed, while silently replacing a cage bond is not.

The assembled molecule deliberately leaves `neighborOrder` empty.  `RawMolecule.writtenNeighbors`
therefore uses its complete bond-list fallback, including every appended bond, rather than reusing
the core parser's now-incomplete per-atom order.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-- Finite data and boundary facts for extending a certified molecular fullerene cage.

Atom identifiers in `extraBonds` address the concatenated atom list: core atoms retain their
indices, and external atom `i` has index `core.atomCount + i`. -/
structure MolecularFullereneDerivativeExtension
    (core : RawMolecule) (carrier : Finset Nat) where
  externalAtoms : List AtomSpec
  extraBonds : List RawBond
  extraBondEndpoints : ∀ bond ∈ extraBonds,
    bond.source < core.atomCount + externalAtoms.length ∧
      bond.target < core.atomCount + externalAtoms.length ∧
        bond.source ≠ bond.target
  /-- Appended edges may meet the cage at one endpoint, but never at both endpoints. -/
  noExtraCageInternalBond : ∀ bond ∈ extraBonds,
    ¬(bond.source ∈ carrier ∧ bond.target ∈ carrier)

namespace MolecularFullereneDerivativeExtension

/-- Append external atoms and bonds, retaining the core indices exactly.  Empty `neighborOrder`
selects the complete bond-list fallback for both the core and the newly attached addends. -/
def assemble {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier) : RawMolecule where
  atoms := core.atoms ++ extension.externalAtoms
  bonds := core.bonds ++ extension.extraBonds
  neighborOrder := []

@[simp] theorem assemble_atoms {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier) :
    extension.assemble.atoms = core.atoms ++ extension.externalAtoms := rfl

@[simp] theorem assemble_bonds {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier) :
    extension.assemble.bonds = core.bonds ++ extension.extraBonds := rfl

@[simp] theorem assemble_neighborOrder {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier) :
    extension.assemble.neighborOrder = [] := rfl

@[simp] theorem assemble_atomCount {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier) :
    extension.assemble.atomCount = core.atomCount + extension.externalAtoms.length := by
  simp [RawMolecule.atomCount, assemble]

/-- Endpoint validity composes with the append construction.  This is deliberately separate from
bond-record uniqueness: concrete derivative rows must also show that they did not duplicate an
unordered edge. -/
theorem assemble_wellFormed {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier)
    (coreWellFormed : core.WellFormed) : extension.assemble.WellFormed := by
  intro bond bondPresent
  rcases List.mem_append.mp bondPresent with coreBond | extraBond
  · obtain ⟨sourceBound, targetBound, distinct⟩ := coreWellFormed bond coreBond
    rw [RawMolecule.BondEndpointsOK, extension.assemble_atomCount]
    exact
      ⟨Nat.lt_of_lt_of_le sourceBound (Nat.le_add_right core.atomCount _),
        Nat.lt_of_lt_of_le targetBound (Nat.le_add_right core.atomCount _), distinct⟩
  · rw [RawMolecule.BondEndpointsOK, extension.assemble_atomCount]
    exact extension.extraBondEndpoints bond extraBond

private theorem listGet?_append_left {Alpha : Type*}
    (left right : List Alpha) (index : Nat) (bound : index < left.length) :
    listGet? (left ++ right) index = listGet? left index := by
  induction left generalizing index with
  | nil => simp at bound
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at bound
          simpa [listGet?] using inductionHypothesis index bound

/-- Appending a derivative is prefix-exact on every core atom. -/
theorem atomAt_core {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier)
    (atom : Nat) (atomBound : atom < core.atomCount) :
    extension.assemble.atomAt? atom = core.atomAt? atom := by
  exact listGet?_append_left core.atoms extension.externalAtoms atom atomBound

private theorem extra_directedConnects_false
    {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier)
    (left right : Nat) (leftPresent : left ∈ carrier) (rightPresent : right ∈ carrier)
    (bond : RawBond) (bondPresent : bond ∈ extension.extraBonds) :
    bond.directedConnects left right = false := by
  by_cases sourceEq : bond.source = left
  · by_cases targetEq : bond.target = right
    · exact False.elim (extension.noExtraCageInternalBond bond bondPresent
        ⟨sourceEq ▸ leftPresent, targetEq ▸ rightPresent⟩)
    · simp [RawBond.directedConnects, sourceEq, targetEq]
  · simp [RawBond.directedConnects, sourceEq]

private theorem foldl_directedBondOrder_eq_of_false
    (bonds : List RawBond) (left right : Nat)
    (neverConnects : ∀ bond ∈ bonds, bond.directedConnects left right = false)
    (initial : BondOrder) :
    bonds.foldl
        (fun order bond =>
          if bond.directedConnects left right then max order bond.kind.order else order)
        initial = initial := by
  induction bonds generalizing initial with
  | nil => rfl
  | cons bond bonds inductionHypothesis =>
      have bondFalse : bond.directedConnects left right = false := neverConnects bond (by simp)
      simp only [List.foldl_cons, bondFalse, Bool.false_eq_true, ↓reduceIte]
      apply inductionHypothesis
      intro extra extraPresent
      exact neverConnects extra (by simp [extraPresent])

private theorem directedBondOrder_on_carrier
    {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier)
    (left right : Nat) (leftPresent : left ∈ carrier) (rightPresent : right ∈ carrier) :
    extension.assemble.directedBondOrder left right = core.directedBondOrder left right := by
  simp only [RawMolecule.directedBondOrder, assemble_bonds, List.foldl_append]
  apply foldl_directedBondOrder_eq_of_false extension.extraBonds left right
  intro bond bondPresent
  exact extension.extra_directedConnects_false
    left right leftPresent rightPresent bond bondPresent

/-- The induced bond-order matrix on the cage carrier is unchanged by arbitrary external
construction satisfying `noExtraCageInternalBond`. -/
theorem bondOrder_on_carrier
    {core : RawMolecule} {carrier : Finset Nat}
    (extension : MolecularFullereneDerivativeExtension core carrier)
    (left right : Nat) (leftPresent : left ∈ carrier) (rightPresent : right ∈ carrier) :
    extension.assemble.bondOrder left right = core.bondOrder left right := by
  unfold RawMolecule.bondOrder
  rw [extension.directedBondOrder_on_carrier left right leftPresent rightPresent,
    extension.directedBondOrder_on_carrier right left rightPresent leftPresent]

/-- A core certificate supplies the bounds needed to turn prefix and bond preservation into the
exact cage-agreement relation consumed by certificate transport. -/
def cageAgreement
    {core : RawMolecule} {package : MolecularFullereneNumberedCagePackage}
    (extension : MolecularFullereneDerivativeExtension core package.carrier)
    (certificate : package.Certificate core) :
    MolecularFullereneCageAgreement core extension.assemble package.carrier := by
  refine
    { derivativeBounds := ?_
      atomAt := ?_
      bondOrder := ?_ }
  · intro atom atomPresent
    obtain ⟨spec, observed, _carbon⟩ :=
      certificate.oriented.1.carbonAtoms atom atomPresent
    have coreBound : atom < core.atomCount :=
      listGet?_eq_some_implies_lt core.atoms atom spec (by
        simpa [RawMolecule.atomAt?] using observed)
    rw [extension.assemble_atomCount]
    exact Nat.lt_of_lt_of_le coreBound (Nat.le_add_right core.atomCount _)
  · intro atom atomPresent
    obtain ⟨spec, observed, _carbon⟩ :=
      certificate.oriented.1.carbonAtoms atom atomPresent
    have coreBound : atom < core.atomCount :=
      listGet?_eq_some_implies_lt core.atoms atom spec (by
        simpa [RawMolecule.atomAt?] using observed)
    exact extension.atomAt_core atom coreBound
  · intro left leftPresent right rightPresent
    exact extension.bondOrder_on_carrier left right leftPresent rightPresent

/-- The major collapse: finite append data transports the complete numbered-cage certificate;
the derivative never re-proves cubicity, connectivity, faces, Euler characteristic, or coherent
orientation. -/
def transportCertificate
    {core : RawMolecule} {package : MolecularFullereneNumberedCagePackage}
    (extension : MolecularFullereneDerivativeExtension core package.carrier)
    (certificate : package.Certificate core) :
    package.Certificate extension.assemble :=
  MolecularFullereneNumberedCagePackage.Certificate.transport
    core extension.assemble package certificate (extension.cageAgreement certificate)

end MolecularFullereneDerivativeExtension

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneDerivativeExtension.atomAt_core
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneDerivativeExtension.bondOrder_on_carrier
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneDerivativeExtension.transportCertificate
