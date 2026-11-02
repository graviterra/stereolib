import TetraStereo.OneCenter.CIPValidationFixtures

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace CIPValidationFixtures

open OneCenter

noncomputable section

theorem officialEdgeFixtureBatch_checked :
    officialCIPEdgeFixtureBatch.AllClaims :=
  officialCIPEdgeFixtureBatch_checked

example :
    officialCIPEdgeFixtures.length = 14 :=
  rfl

example :
    rule3SeqCisSeqTransFixture.expected = Ordering.gt :=
  rfl

example :
    rule4cCrossFamilyTieFixture.expected = Ordering.eq :=
  rfl

example :
    rule5AuxiliaryROverSFixture.artifact.kind = LeanCertificateKind.validationFixture :=
  rfl

example :
    officialCIPEdgeFixtureBatch.toCertificateBatch.AllClaims :=
  officialCIPEdgeFixtureBatch.certificateBatch_checked

example :
    externalValidationIngestionSeed.checkedFixtures.length = 1 :=
  rfl

example :
    externalValidationIngestionSeed.pendingSpecs.length = 1 :=
  rfl

example :
    externalValidationIngestionSeed.checkedFixtureBatch.AllClaims :=
  externalValidationIngestionSeed_checked

end
end CIPValidationFixtures
end Examples
end TetraStereo
