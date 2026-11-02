import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalProfileSuccess
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeSecondSphereProfileSuccess
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
open TetraStereo.UniversalProof.NativeGlobalProfileInventory
open TetraStereo.UniversalProof.NativeChronologicalProfileSuccess

/-- For every actual parity list, the raw tree domain is discharged by the actual constructors.
Only a genuine generated center and actual discovery-root bounds remain as occurrence inputs. -/
theorem family_profile_success (ps : List TetrahedralInputParity) {root : Nat}
    (rootBound : root < (familyRaw ps).atomCount) {center : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode (familyRaw ps) root center) :
    CanonicalTreeProfile.profile? (familyRaw ps) center =
      some ⟨center, ⟨center.history⟩, inventory (familyRaw ps) root ((familyRaw ps).atomCount + 1)⟩ :=
  chronological_profile_success (familyRaw_chronologicalPhysicalTree ps) rootBound generated

/-- A concrete inhabited executable profile request exists for every parity list, including [].
This root request does not claim generation of every written stereocenter or a ranking result. -/
theorem family_root_profile_success (ps : List TetrahedralInputParity) :
    CanonicalTreeProfile.profile? (familyRaw ps) (canonicalCenterRoot 0) =
      some ⟨canonicalCenterRoot 0, ⟨[0]⟩,
        inventory (familyRaw ps) 0 ((familyRaw ps).atomCount + 1)⟩ :=
  family_profile_success ps (familyRaw_chronologicalPhysicalTree ps).1 CanonicalCenterTreeNode.root

end TetraStereo.UniversalProof.NativeSecondSphereProfileSuccess
