import TetraStereo.OneCenter.IUPACP93CanonicalFullereneDerivativePlacements
import TetraStereo.OneCenter.P93MolecularFullereneAddendTemplateCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Frozen local addend graphs for the five P-93.5.6 fullerene examples

This source leaf records the complete local constitutional graph behind each addend kind used by
the five printed derivative rows.  Local atom zero is the attachment atom for every unary
template.  The C70 cyclopropano template is one two-port addend: both cage bonds meet its atom
zero, while its two carboxylate/(1S)-1-phenylbutyl arms remain owned by the same addend.

Hydrogens are implicit except where the printed constitution makes hydrogen itself the addend and
at the two bracket-style stereocentres, whose single hydrogens are recorded explicitly for the
production tetrahedral descriptor computation.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

private def atom (element : Element) : AtomSpec := AtomSpec.aliphatic element

private def aromaticCarbon : AtomSpec := AtomSpec.aromaticAtom .C

private def chiralCarbonSInput : AtomSpec :=
  { AtomSpec.aliphatic .C with
      explicitHydrogens? := some 1
      tetrahedral? := some .clockwise }

private def bridgeCarbon : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some 0 }

private def bond (source target : Nat) (kind : ParsedBondKind := .single) : RawBond :=
  { source := source, target := target, kind := kind }

private def unaryPort {externalAtomCount : Nat} (externalAtom : Fin externalAtomCount) :
    Fin 1 → MolecularFullereneLocalAddendPort externalAtomCount :=
  fun _ => { externalAtom := externalAtom, bondKind := .single }

/-! ## Executable connectedness bridge -/

private def localConnectivityPackage (template : MolecularFullereneLocalAddendTemplate) :
    MolecularFullereneNumberedCagePackage where
  atomsByLocant := List.range template.externalAtoms.length
  edgeTable := []
  faces := []

private def commonPrefixLength : List Nat → List Nat → Nat
  | first :: firstRest, second :: secondRest =>
      if first = second then 1 + commonPrefixLength firstRest secondRest else 0
  | _, _ => 0

/-- The simple route in a rooted spanning tree described by root-to-vertex paths. -/
private def localTreeRoute (rootPath : Nat → List Nat) (first second : Nat) : List Nat :=
  let firstPath := rootPath first
  let secondPath := rootPath second
  let common := commonPrefixLength firstPath secondPath
  (firstPath.drop (common - 1)).reverse ++ secondPath.drop common

private def localTreeRoutes (rootPath : Nat → List Nat) :
    MolecularFullereneExplicitRoutes where
  route := localTreeRoute rootPath

private theorem localTemplateValid_of_checkedRoutes
    (template : MolecularFullereneLocalAddendTemplate)
    (rootPath : Nat → List Nat)
    (identityPositive : 0 < template.identityClass)
    (portsPositive : 0 < template.portCount)
    (uniqueEdges : template.internalBonds.Pairwise fun first second =>
      first.edgeKey ≠ second.edgeKey)
    (endpointsAccepted : template.localMolecule.bonds.all
      (template.localMolecule.bondEndpointsOK?) = true)
    (atomsNonempty : template.externalAtoms ≠ [])
    (routesAccepted : molecularFullereneAllRoutesAccepted template.localMolecule
      (localConnectivityPackage template) (localTreeRoutes rootPath) = true) :
    template.Valid := by
  refine ⟨identityPositive, portsPositive, uniqueEdges, ?_, ?_⟩
  · have wellFormed : template.localMolecule.WellFormed :=
      (template.localMolecule.wellFormed_iff_all_bondEndpointsOK).mpr endpointsAccepted
    intro rawBond rawBondPresent
    simpa [MolecularFullereneLocalAddendTemplate.localMolecule,
      RawMolecule.BondEndpointsOK, RawMolecule.atomCount] using
      wellFormed rawBond rawBondPresent
  · have connected := molecularFullereneCageConnected_of_allRoutesAccepted
      template.localMolecule (localConnectivityPackage template)
      (localTreeRoutes rootPath) (by
        change List.range template.externalAtoms.length ≠ []
        intro rangeEmpty
        have lengthZero : template.externalAtoms.length = 0 := by
          have := congrArg List.length rangeEmpty
          simpa using this
        exact atomsNonempty (List.length_eq_zero_iff.mp lengthZero)) routesAccepted
    have carrierExact :
        (localConnectivityPackage template).carrier =
          Finset.range template.externalAtoms.length := by
      ext localAtom
      simp [localConnectivityPackage, MolecularFullereneNumberedCagePackage.carrier]
    intro first second
    simpa only [carrierExact] using connected.2 first
      (by simp [localConnectivityPackage, MolecularFullereneNumberedCagePackage.carrier])
      second
      (by simp [localConnectivityPackage, MolecularFullereneNumberedCagePackage.carrier])

/-! ## Hydrogen -/

def iupacP93CanonicalFullereneHydrogenTemplate : MolecularFullereneLocalAddendTemplate where
  externalAtoms := [atom .H]
  internalBonds := []
  portCount := 1
  port := unaryPort ⟨0, by decide⟩
  identityClass := 1
  intrinsicallyChiral := false

private def hydrogenRootPath : Nat → List Nat
  | 0 => [0]
  | _ => []

theorem iupacP93CanonicalFullereneHydrogenTemplate_valid :
    iupacP93CanonicalFullereneHydrogenTemplate.Valid := by
  apply localTemplateValid_of_checkedRoutes _ hydrogenRootPath
  all_goals decide

/-! ## tert-Butyl -/

def iupacP93CanonicalFullereneTertButylTemplate : MolecularFullereneLocalAddendTemplate where
  externalAtoms := List.replicate 4 (atom .C)
  internalBonds := [bond 0 1, bond 0 2, bond 0 3]
  portCount := 1
  port := unaryPort ⟨0, by decide⟩
  identityClass := 2
  intrinsicallyChiral := false

private def tertButylRootPath : Nat → List Nat
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 2]
  | 3 => [0, 3]
  | _ => []

theorem iupacP93CanonicalFullereneTertButylTemplate_valid :
    iupacP93CanonicalFullereneTertButylTemplate.Valid := by
  apply localTemplateValid_of_checkedRoutes _ tertButylRootPath
  all_goals decide

/-! ## 1,1,1,3,3,3-Hexamethyl-2-(trimethylsilyl)trisilan-2-yl -/

def iupacP93CanonicalFullereneTrisilylTemplate : MolecularFullereneLocalAddendTemplate where
  externalAtoms := List.replicate 4 (atom .Si) ++ List.replicate 9 (atom .C)
  internalBonds :=
    [ bond 0 1, bond 0 2, bond 0 3,
      bond 1 4, bond 1 5, bond 1 6,
      bond 2 7, bond 2 8, bond 2 9,
      bond 3 10, bond 3 11, bond 3 12 ]
  portCount := 1
  port := unaryPort ⟨0, by decide⟩
  identityClass := 3
  intrinsicallyChiral := false

private def trisilylRootPath : Nat → List Nat
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 2]
  | 3 => [0, 3]
  | 4 => [0, 1, 4]
  | 5 => [0, 1, 5]
  | 6 => [0, 1, 6]
  | 7 => [0, 2, 7]
  | 8 => [0, 2, 8]
  | 9 => [0, 2, 9]
  | 10 => [0, 3, 10]
  | 11 => [0, 3, 11]
  | 12 => [0, 3, 12]
  | _ => []

theorem iupacP93CanonicalFullereneTrisilylTemplate_valid :
    iupacP93CanonicalFullereneTrisilylTemplate.Valid := by
  apply localTemplateValid_of_checkedRoutes _ trisilylRootPath
  all_goals decide

/-! ## 3,6-Dicyclopropylcyclohepta-2,4,6-trien-1-yl -/

def iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate :
    MolecularFullereneLocalAddendTemplate where
  externalAtoms := List.replicate 13 (atom .C)
  internalBonds :=
    [ bond 0 1, bond 1 2 .double, bond 2 3, bond 3 4 .double,
      bond 4 5, bond 5 6 .double, bond 6 0,
      bond 2 7, bond 7 8, bond 8 9, bond 9 7,
      bond 5 10, bond 10 11, bond 11 12, bond 12 10 ]
  portCount := 1
  port := unaryPort ⟨0, by decide⟩
  identityClass := 4
  intrinsicallyChiral := false

private def dicyclopropylCycloheptatrienylRootPath : Nat → List Nat
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 2]
  | 3 => [0, 1, 2, 3]
  | 4 => [0, 1, 2, 3, 4]
  | 5 => [0, 6, 5]
  | 6 => [0, 6]
  | 7 => [0, 1, 2, 7]
  | 8 => [0, 1, 2, 7, 8]
  | 9 => [0, 1, 2, 7, 9]
  | 10 => [0, 6, 5, 10]
  | 11 => [0, 6, 5, 10, 11]
  | 12 => [0, 6, 5, 10, 12]
  | _ => []

theorem iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate_valid :
    iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.Valid := by
  apply localTemplateValid_of_checkedRoutes _ dicyclopropylCycloheptatrienylRootPath
  all_goals decide

/-! ## Two-port cyclopropano bis(carboxylate) bearing two (1S)-1-phenylbutyl groups -/

def iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylAtoms : List AtomSpec :=
  [ bridgeCarbon,
    atom .C, atom .O, atom .O, chiralCarbonSInput, atom .C, atom .C, atom .C,
    aromaticCarbon, aromaticCarbon, aromaticCarbon, aromaticCarbon, aromaticCarbon, aromaticCarbon,
    atom .C, atom .O, atom .O, chiralCarbonSInput, atom .C, atom .C, atom .C,
    aromaticCarbon, aromaticCarbon, aromaticCarbon, aromaticCarbon, aromaticCarbon, aromaticCarbon ]

def iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds : List RawBond :=
  [ bond 0 1, bond 1 2 .double, bond 1 3, bond 3 4,
    bond 4 5, bond 5 6, bond 6 7, bond 4 8,
    bond 8 9 .aromatic, bond 9 10 .aromatic, bond 10 11 .aromatic,
    bond 11 12 .aromatic, bond 12 13 .aromatic, bond 13 8 .aromatic,
    bond 0 14, bond 14 15 .double, bond 14 16, bond 16 17,
    bond 17 18, bond 18 19, bond 19 20, bond 17 21,
    bond 21 22 .aromatic, bond 22 23 .aromatic, bond 23 24 .aromatic,
    bond 24 25 .aromatic, bond 25 26 .aromatic, bond 26 21 .aromatic ]

def iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate :
    MolecularFullereneLocalAddendTemplate where
  externalAtoms := iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylAtoms
  internalBonds := iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds
  portCount := 2
  port := fun _ => { externalAtom := ⟨0, by decide⟩, bondKind := .single }
  identityClass := 5
  intrinsicallyChiral := true

private def cyclopropanoBisCarboxylatePhenylbutylRootPath : Nat → List Nat
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 2]
  | 3 => [0, 1, 3]
  | 4 => [0, 1, 3, 4]
  | 5 => [0, 1, 3, 4, 5]
  | 6 => [0, 1, 3, 4, 5, 6]
  | 7 => [0, 1, 3, 4, 5, 6, 7]
  | 8 => [0, 1, 3, 4, 8]
  | 9 => [0, 1, 3, 4, 8, 9]
  | 10 => [0, 1, 3, 4, 8, 9, 10]
  | 11 => [0, 1, 3, 4, 8, 9, 10, 11]
  | 12 => [0, 1, 3, 4, 8, 13, 12]
  | 13 => [0, 1, 3, 4, 8, 13]
  | 14 => [0, 14]
  | 15 => [0, 14, 15]
  | 16 => [0, 14, 16]
  | 17 => [0, 14, 16, 17]
  | 18 => [0, 14, 16, 17, 18]
  | 19 => [0, 14, 16, 17, 18, 19]
  | 20 => [0, 14, 16, 17, 18, 19, 20]
  | 21 => [0, 14, 16, 17, 21]
  | 22 => [0, 14, 16, 17, 21, 22]
  | 23 => [0, 14, 16, 17, 21, 22, 23]
  | 24 => [0, 14, 16, 17, 21, 22, 23, 24]
  | 25 => [0, 14, 16, 17, 21, 26, 25]
  | 26 => [0, 14, 16, 17, 21, 26]
  | _ => []

theorem iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_valid :
    iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.Valid := by
  apply localTemplateValid_of_checkedRoutes _ cyclopropanoBisCarboxylatePhenylbutylRootPath
  all_goals decide

/-! ## Frozen size, port, ordering, and stereochemical facts -/

/-- Exact literal constitution of the hydrogen addend, including its only attachment port. -/
theorem iupacP93CanonicalFullereneHydrogenTemplate_constitution :
    iupacP93CanonicalFullereneHydrogenTemplate.externalAtoms =
        [{ element := .H }] ∧
      iupacP93CanonicalFullereneHydrogenTemplate.internalBonds = [] ∧
      iupacP93CanonicalFullereneHydrogenTemplate.portCount = 1 ∧
      iupacP93CanonicalFullereneHydrogenTemplate.identityClass = 1 ∧
      iupacP93CanonicalFullereneHydrogenTemplate.intrinsicallyChiral = false ∧
      (∀ portIndex,
        (iupacP93CanonicalFullereneHydrogenTemplate.port portIndex).externalAtom.val = 0 ∧
          (iupacP93CanonicalFullereneHydrogenTemplate.port portIndex).bondKind = .single) := by
  decide

/-- Exact literal constitution of tert-butyl, including all three C--C bonds and its port. -/
theorem iupacP93CanonicalFullereneTertButylTemplate_constitution :
    iupacP93CanonicalFullereneTertButylTemplate.externalAtoms =
        [{ element := .C }, { element := .C }, { element := .C }, { element := .C }] ∧
      iupacP93CanonicalFullereneTertButylTemplate.internalBonds =
        [{ source := 0, target := 1, kind := .single },
         { source := 0, target := 2, kind := .single },
         { source := 0, target := 3, kind := .single }] ∧
      iupacP93CanonicalFullereneTertButylTemplate.portCount = 1 ∧
      iupacP93CanonicalFullereneTertButylTemplate.identityClass = 2 ∧
      iupacP93CanonicalFullereneTertButylTemplate.intrinsicallyChiral = false ∧
      (∀ portIndex,
        (iupacP93CanonicalFullereneTertButylTemplate.port portIndex).externalAtom.val = 0 ∧
          (iupacP93CanonicalFullereneTertButylTemplate.port portIndex).bondKind = .single) := by
  decide

/-- Exact literal constitution of the Si4C9 trisilyl addend and its attachment port. -/
theorem iupacP93CanonicalFullereneTrisilylTemplate_constitution :
    iupacP93CanonicalFullereneTrisilylTemplate.externalAtoms =
        [{ element := .Si }, { element := .Si }, { element := .Si }, { element := .Si },
         { element := .C }, { element := .C }, { element := .C },
         { element := .C }, { element := .C }, { element := .C },
         { element := .C }, { element := .C }, { element := .C }] ∧
      iupacP93CanonicalFullereneTrisilylTemplate.internalBonds =
        [{ source := 0, target := 1, kind := .single },
         { source := 0, target := 2, kind := .single },
         { source := 0, target := 3, kind := .single },
         { source := 1, target := 4, kind := .single },
         { source := 1, target := 5, kind := .single },
         { source := 1, target := 6, kind := .single },
         { source := 2, target := 7, kind := .single },
         { source := 2, target := 8, kind := .single },
         { source := 2, target := 9, kind := .single },
         { source := 3, target := 10, kind := .single },
         { source := 3, target := 11, kind := .single },
         { source := 3, target := 12, kind := .single }] ∧
      iupacP93CanonicalFullereneTrisilylTemplate.portCount = 1 ∧
      iupacP93CanonicalFullereneTrisilylTemplate.identityClass = 3 ∧
      iupacP93CanonicalFullereneTrisilylTemplate.intrinsicallyChiral = false ∧
      (∀ portIndex,
        (iupacP93CanonicalFullereneTrisilylTemplate.port portIndex).externalAtom.val = 0 ∧
          (iupacP93CanonicalFullereneTrisilylTemplate.port portIndex).bondKind = .single) := by
  decide

/-- Exact literal constitution of 3,6-dicyclopropylcyclohepta-2,4,6-trien-1-yl. -/
theorem iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate_constitution :
    iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.externalAtoms =
        [{ element := .C }, { element := .C }, { element := .C }, { element := .C },
         { element := .C }, { element := .C }, { element := .C }, { element := .C },
         { element := .C }, { element := .C }, { element := .C }, { element := .C },
         { element := .C }] ∧
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.internalBonds =
        [{ source := 0, target := 1, kind := .single },
         { source := 1, target := 2, kind := .double },
         { source := 2, target := 3, kind := .single },
         { source := 3, target := 4, kind := .double },
         { source := 4, target := 5, kind := .single },
         { source := 5, target := 6, kind := .double },
         { source := 6, target := 0, kind := .single },
         { source := 2, target := 7, kind := .single },
         { source := 7, target := 8, kind := .single },
         { source := 8, target := 9, kind := .single },
         { source := 9, target := 7, kind := .single },
         { source := 5, target := 10, kind := .single },
         { source := 10, target := 11, kind := .single },
         { source := 11, target := 12, kind := .single },
         { source := 12, target := 10, kind := .single }] ∧
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.portCount = 1 ∧
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.identityClass = 4 ∧
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.intrinsicallyChiral = false ∧
      (∀ portIndex,
        (iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.port portIndex).externalAtom.val = 0 ∧
          (iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.port
            portIndex).bondKind = .single) := by
  decide

/--
Exact literal constitution of the single two-port C70 addend.  The statement independently freezes
the H0 bridge carbon, both complete ester/(1S)-1-phenylbutyl arms, both aromatic phenyl rings, both
clockwise H1 tetrahedral inputs, and every attachment port as a single bond to bridge atom zero.
-/
theorem iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_constitution :
    iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.externalAtoms =
        [{ element := .C, explicitHydrogens? := some 0 },
         { element := .C }, { element := .O }, { element := .O },
         { element := .C, explicitHydrogens? := some 1,
           tetrahedral? := some .clockwise },
         { element := .C }, { element := .C }, { element := .C },
         { element := .C, aromatic := true }, { element := .C, aromatic := true },
         { element := .C, aromatic := true }, { element := .C, aromatic := true },
         { element := .C, aromatic := true }, { element := .C, aromatic := true },
         { element := .C }, { element := .O }, { element := .O },
         { element := .C, explicitHydrogens? := some 1,
           tetrahedral? := some .clockwise },
         { element := .C }, { element := .C }, { element := .C },
         { element := .C, aromatic := true }, { element := .C, aromatic := true },
         { element := .C, aromatic := true }, { element := .C, aromatic := true },
         { element := .C, aromatic := true }, { element := .C, aromatic := true }] ∧
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.internalBonds =
        [{ source := 0, target := 1, kind := .single },
         { source := 1, target := 2, kind := .double },
         { source := 1, target := 3, kind := .single },
         { source := 3, target := 4, kind := .single },
         { source := 4, target := 5, kind := .single },
         { source := 5, target := 6, kind := .single },
         { source := 6, target := 7, kind := .single },
         { source := 4, target := 8, kind := .single },
         { source := 8, target := 9, kind := .aromatic },
         { source := 9, target := 10, kind := .aromatic },
         { source := 10, target := 11, kind := .aromatic },
         { source := 11, target := 12, kind := .aromatic },
         { source := 12, target := 13, kind := .aromatic },
         { source := 13, target := 8, kind := .aromatic },
         { source := 0, target := 14, kind := .single },
         { source := 14, target := 15, kind := .double },
         { source := 14, target := 16, kind := .single },
         { source := 16, target := 17, kind := .single },
         { source := 17, target := 18, kind := .single },
         { source := 18, target := 19, kind := .single },
         { source := 19, target := 20, kind := .single },
         { source := 17, target := 21, kind := .single },
         { source := 21, target := 22, kind := .aromatic },
         { source := 22, target := 23, kind := .aromatic },
         { source := 23, target := 24, kind := .aromatic },
         { source := 24, target := 25, kind := .aromatic },
         { source := 25, target := 26, kind := .aromatic },
         { source := 26, target := 21, kind := .aromatic }] ∧
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.portCount = 2 ∧
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.identityClass = 5 ∧
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.intrinsicallyChiral = true ∧
      (∀ portIndex,
        (iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.port
          portIndex).externalAtom.val = 0 ∧
          (iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.port
            portIndex).bondKind = .single) := by
  decide

theorem iupacP93CanonicalFullereneAddendTemplateCounts :
    (iupacP93CanonicalFullereneHydrogenTemplate.externalAtoms.length,
        iupacP93CanonicalFullereneHydrogenTemplate.internalBonds.length,
        iupacP93CanonicalFullereneHydrogenTemplate.portCount) = (1, 0, 1) ∧
      (iupacP93CanonicalFullereneTertButylTemplate.externalAtoms.length,
        iupacP93CanonicalFullereneTertButylTemplate.internalBonds.length,
        iupacP93CanonicalFullereneTertButylTemplate.portCount) = (4, 3, 1) ∧
      (iupacP93CanonicalFullereneTrisilylTemplate.externalAtoms.length,
        iupacP93CanonicalFullereneTrisilylTemplate.internalBonds.length,
        iupacP93CanonicalFullereneTrisilylTemplate.portCount) = (13, 12, 1) ∧
      (iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.externalAtoms.length,
        iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.internalBonds.length,
        iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.portCount) = (13, 15, 1) ∧
      (iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.externalAtoms.length,
        iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.internalBonds.length,
        iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.portCount) =
          (27, 28, 2) := by
  decide

theorem iupacP93CanonicalFullereneCyclopropanoTemplate_ports_share_bridge :
    ∀ portIndex : Fin 2,
      (iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.port
        portIndex).externalAtom = ⟨0, by decide⟩ := by
  intro portIndex
  rfl

theorem iupacP93CanonicalFullereneCyclopropanoTemplate_bonds_frozen :
    iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.internalBonds =
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylBonds := rfl

set_option maxRecDepth 100000 in
theorem iupacP93CanonicalFullereneCyclopropanoTemplate_materialized_center_orders :
    let expanded :=
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.localMolecule
        |>.withExplicitHydrogens
    expanded.writtenNeighbors 4 = [3, 27, 5, 8] ∧
      expanded.writtenNeighbors 17 = [16, 40, 18, 21] := by
  decide

set_option maxRecDepth 100000 in
theorem iupacP93CanonicalFullereneCyclopropanoTemplate_first_center_is_S :
    parsedTetrahedralDescriptorAt?
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.localMolecule 4 =
        some .S := by
  decide

set_option maxRecDepth 100000 in
theorem iupacP93CanonicalFullereneCyclopropanoTemplate_second_center_is_S :
    parsedTetrahedralDescriptorAt?
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.localMolecule 17 =
        some .S := by
  decide

theorem iupacP93CanonicalFullereneAddendTemplates_valid :
    iupacP93CanonicalFullereneHydrogenTemplate.Valid ∧
      iupacP93CanonicalFullereneTertButylTemplate.Valid ∧
      iupacP93CanonicalFullereneTrisilylTemplate.Valid ∧
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate.Valid ∧
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.Valid := by
  exact ⟨iupacP93CanonicalFullereneHydrogenTemplate_valid,
    iupacP93CanonicalFullereneTertButylTemplate_valid,
    iupacP93CanonicalFullereneTrisilylTemplate_valid,
    iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate_valid,
    iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_valid⟩

/-- Total source-kind compiler used by all five derivative placement ledgers. -/
def IUPACP93PrintedFullereneAddendKind.localTemplate :
    IUPACP93PrintedFullereneAddendKind → MolecularFullereneLocalAddendTemplate
  | .hydrogen => iupacP93CanonicalFullereneHydrogenTemplate
  | .tertButyl => iupacP93CanonicalFullereneTertButylTemplate
  | .trisilyl => iupacP93CanonicalFullereneTrisilylTemplate
  | .dicyclopropylCycloheptatrienyl =>
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate
  | .cyclopropanoBisCarboxylatePhenylbutyl =>
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate

theorem IUPACP93PrintedFullereneAddendKind.localTemplate_valid
    (kind : IUPACP93PrintedFullereneAddendKind) : kind.localTemplate.Valid := by
  cases kind with
  | hydrogen => exact iupacP93CanonicalFullereneHydrogenTemplate_valid
  | tertButyl => exact iupacP93CanonicalFullereneTertButylTemplate_valid
  | trisilyl => exact iupacP93CanonicalFullereneTrisilylTemplate_valid
  | dicyclopropylCycloheptatrienyl =>
      exact iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate_valid
  | cyclopropanoBisCarboxylatePhenylbutyl =>
      exact iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_valid

theorem IUPACP93PrintedFullereneAddendKind.localTemplate_portCount
    (kind : IUPACP93PrintedFullereneAddendKind) :
    kind.localTemplate.portCount =
      if kind = .cyclopropanoBisCarboxylatePhenylbutyl then 2 else 1 := by
  cases kind <;> decide

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneAddendTemplates_valid
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneCyclopropanoTemplate_first_center_is_S
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneCyclopropanoTemplate_second_center_is_S
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneHydrogenTemplate_constitution
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneTertButylTemplate_constitution
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneTrisilylTemplate_constitution
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate_constitution
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_constitution
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.IUPACP93PrintedFullereneAddendKind.localTemplate_valid
