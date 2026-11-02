import TetraStereo.OneCenter.CarbohydrateGlycosideRingSystemSemantics

set_option autoImplicit false









namespace TetraStereo.OneCenter
namespace CarbohydrateLateImageMeaningData

inductive ImageFamily where
  | oSubstitution | nSubstitution | intramolecularAnhydride
  | intermolecularAnhydride | cyclicAcetal | carbonylDerivative
  | residue | radical | cation | anion | radicalIon
  | glycoside | thioglycoside | selenoglycoside | glycosylHalide
  | glycosylamine | carbonGlycosyl | ringHeteroReplacement | ringCarbonReplacement
  | bridgedRing | fusedRing | spiro
  deriving DecidableEq, Repr, Inhabited

inductive AttachmentAtom where
  | O | N | S | Se | C | P | halogen
  deriving DecidableEq, Repr, Inhabited

inductive ElectronicState where
  | neutral | radical | cation | anion | radicalCation | radicalAnion
  deriving DecidableEq, Repr, Inhabited

inductive AbsoluteConfiguration where
  | R | S
  deriving DecidableEq, Repr, Inhabited

inductive AddedRingKind where
  | bridge | fusion | spiro
  deriving DecidableEq, Repr, Inhabited

inductive StructuralFeature where
  | heteroSubstitution (atom : AttachmentAtom) (locants : List Nat) (groupName : String)
  | phosphorusOrSulfurEster (element : AttachmentAtom) (locants : List Nat)
      (esterKind : String)
  | anhydroBridge (firstLocant secondLocant : Nat)
  | intermolecularBridge (firstResidue firstLocant secondResidue secondLocant : Nat)
  | acetalBridge (locants : List Nat) (heteroAtoms : List AttachmentAtom)
      (newCenterConfiguration? : Option AbsoluteConfiguration)
  | carbonylDerivative (carbonLocant : Nat) (heteroAtoms : List AttachmentAtom)
      (newCenterConfiguration? : Option AbsoluteConfiguration)
  | freeValence (locant : Nat) (attachment : AttachmentAtom) (multiplicity : Nat)
  | electronicCenter (locant : Nat) (atom : AttachmentAtom) (state : ElectronicState)
  | glycosidicLink (donorLocant : Nat) (atom : AttachmentAtom) (acceptorDescription : String)
  | ringReplacement (locant : Nat) (replacement : AttachmentAtom)
  | addedRing (kind : AddedRingKind) (junctionLocants : List Nat)
      (junctionAtoms : List AttachmentAtom)
  | modification (locants : List Nat) (name : String)
  | carbohydrateResidueCount (count : Nat)
  | depictionMeaning (description : String)
  deriving DecidableEq, Repr, Inhabited

structure ImageMeaning where
  family : ImageFamily
  sourceKey : String
  acceptedNames : List String
  discouragedNames : List String := []
  trivialNames : List String := []
  features : List StructuralFeature
  structuralVariantCount : Nat := 1
  depictionCount : Nat := 1
  deriving DecidableEq, Repr, Inhabited

def positiveLocants (locants : List Nat) : Bool :=
  !locants.isEmpty && locants.all fun locant => decide (0 < locant)

def StructuralFeature.wellFormed : StructuralFeature → Bool
  | .heteroSubstitution _ locants groupName => positiveLocants locants && !groupName.isEmpty
  | .phosphorusOrSulfurEster atom locants esterKind =>
      decide (atom = .P ∨ atom = .S) && positiveLocants locants && !esterKind.isEmpty
  | .anhydroBridge first second => decide (0 < first ∧ 0 < second ∧ first ≠ second)
  | .intermolecularBridge firstResidue firstLocant secondResidue secondLocant =>
      decide (0 < firstResidue ∧ 0 < firstLocant ∧ 0 < secondResidue ∧ 0 < secondLocant ∧
        firstResidue ≠ secondResidue)
  | .acetalBridge locants atoms _ => positiveLocants locants && !atoms.isEmpty
  | .carbonylDerivative carbonLocant atoms _ => decide (0 < carbonLocant) && !atoms.isEmpty
  | .freeValence locant _ multiplicity => decide (0 < locant ∧ 0 < multiplicity)
  | .electronicCenter locant _ _ => decide (0 < locant)
  | .glycosidicLink donorLocant _ acceptorDescription =>
      decide (0 < donorLocant) && !acceptorDescription.isEmpty
  | .ringReplacement locant _ => decide (0 < locant)
  | .addedRing _ junctionLocants junctionAtoms =>
      positiveLocants junctionLocants && !junctionAtoms.isEmpty
  | .modification locants name => positiveLocants locants && !name.isEmpty
  | .carbohydrateResidueCount count => decide (0 < count)
  | .depictionMeaning description => !description.isEmpty

def ImageMeaning.wellFormed (meaning : ImageMeaning) : Bool :=
  !meaning.sourceKey.isEmpty && !meaning.acceptedNames.isEmpty &&
    meaning.acceptedNames.all (fun name => !name.isEmpty) &&
    !meaning.features.isEmpty && meaning.features.all StructuralFeature.wellFormed &&
    decide (0 < meaning.structuralVariantCount ∧ 0 < meaning.depictionCount)

def textMeaning (family : ImageFamily) (sourceKey printedText : String)
    (features : List StructuralFeature) (structuralVariantCount : Nat := 1)
    (depictionCount : Nat := 1) : ImageMeaning :=
  { family, sourceKey, acceptedNames := [printedText], features,
    structuralVariantCount, depictionCount }

end CarbohydrateLateImageMeaningData
end TetraStereo.OneCenter
