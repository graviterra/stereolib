import TetraStereo.OneCenter.OfficialNoncenterDetectors

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialNoncenterDetectors

open OneCenter

def demoBundle : OfficialNoncenterDetectorBundle (Fin 4) where
  doubleBonds :=
    [{ left := 1, right := 2, stereo? := some DoubleBondStereo.E }]
  cumulenes :=
    [{ path := [0, 1, 2], stereo? := some DoubleBondStereo.Z }]
  helices :=
    [{ unit :=
        { helixPath := [0, 1, 2]
          frontReference := 0
          backReference := 2 }
       descriptor := HelicalDescriptor.M }]
  conformations :=
    [{ support := [0, 1, 2, 3].toFinset
       kind? := some OfficialStereogenicUnitKind.chiral }]
  auxiliaryRule5Nodes :=
    [{ anchor := 3
       support := [3].toFinset
       descriptor := OfficialRule5Descriptor.descriptorR
       rootDistance? := some 0 }]
  phantomNodes :=
    [{ anchor := 0
       support := [0].toFinset
       rootDistance? := some 1 }]
  lonePairNodes :=
    [{ anchor := 2
       support := [2].toFinset
       rootDistance? := some 2 }]

/-- A coverage-oriented detector bundle with every broad non-center family present. -/
def completeSurfaceBundle : OfficialNoncenterDetectorBundle (Fin 6) where
  doubleBonds :=
    [{ left := 0, right := 1, stereo? := some DoubleBondStereo.Z }]
  cumulenes :=
    [{ path := [1, 2, 3], stereo? := none }]
  axes :=
    [{ unit :=
        { axisStart := 0
          axisEnd := 1
          startHigh := 2
          startLow := 3
          endHigh := 4
          endLow := 5 }
       descriptor := AxialDescriptor.Ra }]
  planes :=
    [{ unit :=
        { planeAtoms := [0, 1, 2]
          pilotAtom := 3
          highReference := 4
          lowReference := 5 }
       descriptor := PlanarDescriptor.Rp }]
  helices :=
    [{ unit :=
        { helixPath := [0, 2, 4]
          frontReference := 1
          backReference := 5 }
       descriptor := HelicalDescriptor.P }]
  conformations :=
    [{ support := [0, 1, 2, 3, 4, 5].toFinset
       kind? := some OfficialStereogenicUnitKind.chiral }]
  ensembles :=
    [{ support := [0, 1, 2, 3, 4, 5].toFinset
       kind? := some OfficialStereogenicUnitKind.chiral }]
  auxiliaryRule5Nodes :=
    [{ anchor := 4
       support := [4].toFinset
       descriptor := OfficialRule5Descriptor.descriptorS
       rootDistance? := some 1 }]
  phantomNodes :=
    [{ anchor := 5
       support := [5].toFinset
       rootDistance? := some 2 }]
  lonePairNodes :=
    [{ anchor := 3
       support := [3].toFinset
       rootDistance? := some 3 }]

noncomputable def demoDetection : OfficialUnitDetectionResult (Fin 4) :=
  demoBundle.toDetectionResult

noncomputable def completeSurfaceDetection : OfficialUnitDetectionResult (Fin 6) :=
  completeSurfaceBundle.toDetectionResult

example :
    completeSurfaceBundle.coverage.coversBroadStereochemicalSurface = true :=
  rfl

example :
    completeSurfaceDetection.units.length = 10 :=
  rfl

example :
    (completeSurfaceDetection.unitsOfKind OfficialStereochemicalUnitKind.axis).length = 1 :=
  rfl

example :
    (completeSurfaceDetection.unitsOfKind OfficialStereochemicalUnitKind.plane).length = 1 :=
  rfl

example :
    (completeSurfaceDetection.unitsOfKind OfficialStereochemicalUnitKind.ensemble).length = 1 :=
  rfl

def demoUnit0 : demoDetection.Unit :=
  ⟨0, by
    simp [demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
      OfficialNoncenterDetectorBundle.detectedUnits]⟩

def demoUnit1 : demoDetection.Unit :=
  ⟨1, by
    simp [demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
      OfficialNoncenterDetectorBundle.detectedUnits]⟩

def demoUnit2 : demoDetection.Unit :=
  ⟨2, by
    simp [demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
      OfficialNoncenterDetectorBundle.detectedUnits]⟩

def demoUnit4 : demoDetection.Unit :=
  ⟨4, by
    simp [demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
      OfficialNoncenterDetectorBundle.detectedUnits]⟩

def demoUnit5 : demoDetection.Unit :=
  ⟨5, by
    simp [demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
      OfficialNoncenterDetectorBundle.detectedUnits]⟩

def demoUnit6 : demoDetection.Unit :=
  ⟨6, by
    simp [demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
      OfficialNoncenterDetectorBundle.detectedUnits]⟩

example :
    demoDetection.units.length = 7 :=
  rfl

example :
    demoDetection.initialEnvironment.rule3Geometry demoUnit0 =
      some OfficialRule3Geometry.seqtrans :=
  by
    rfl

example :
    demoDetection.initialEnvironment.rule3Geometry demoUnit1 =
      some OfficialRule3Geometry.seqcis :=
  by
    rfl

example :
    demoDetection.initialEnvironment.rule5Descriptor demoUnit2 =
      some OfficialRule5Descriptor.descriptorM :=
  by
    rfl

example :
    demoDetection.initialEnvironment.rule5Descriptor demoUnit4 =
      some OfficialRule5Descriptor.descriptorR.asAuxiliary :=
  by
    rfl

example :
    demoDetection.nodeKind? demoUnit4 = some OfficialPhantomNodeKind.auxiliary :=
  by
    rfl

example :
    demoDetection.nodeRootDistance? demoUnit4 = some 0 :=
  by
    rfl

example :
    demoDetection.nodeKind? demoUnit5 = some OfficialPhantomNodeKind.phantom :=
  by
    rfl

example :
    demoDetection.nodeRootDistance? demoUnit5 = some 1 :=
  by
    rfl

example :
    demoDetection.nodeKind? demoUnit6 = some OfficialPhantomNodeKind.lonePair :=
  by
    rfl

example :
    demoDetection.nodeRootDistance? demoUnit6 = some 2 :=
  by
    rfl

example :
    demoUnit4 ∈ demoDetection.unitsAtVirtualNodeByKind OfficialPhantomNodeKind.auxiliary := by
  rw [demoDetection.mem_unitsAtVirtualNodeByKind_iff]
  rfl

example :
    demoUnit4 ∈
      demoDetection.unitsAtVirtualNodeByKindDistance OfficialPhantomNodeKind.auxiliary 0 := by
  rw [demoDetection.mem_unitsAtVirtualNodeByKindDistance_iff]
  exact ⟨rfl, rfl⟩

example :
    demoUnit5 ∈ demoDetection.unitsAtVirtualNodeByKind OfficialPhantomNodeKind.phantom := by
  rw [demoDetection.mem_unitsAtVirtualNodeByKind_iff]
  rfl

example (m : OneCenter.MultiCenterMolecule (Fin 4)) (center : m.Center) (i : Fin 4) :
    (m.officialNodeDescriptorUnitSources demoDetection.initialEnvironment
      (demoDetection.descriptorSourceBranchPolicy m) center i
      [OfficialCIPNode.auxiliary (V := Fin 4) 0]).length = 1 := by
  rfl

example (m : OneCenter.MultiCenterMolecule (Fin 4)) (center : m.Center) (i : Fin 4) :
    (officialContextOfDescriptorUnitSources demoDetection.initialEnvironment
      (m.officialNodeDescriptorUnitSources demoDetection.initialEnvironment
        (demoDetection.descriptorSourceBranchPolicy m) center i
        [OfficialCIPNode.auxiliary (V := Fin 4) 0])).rule5Descriptor? =
        some OfficialRule5Descriptor.descriptorR.asAuxiliary := by
  rfl

example (m : OneCenter.MultiCenterMolecule (Fin 4)) (center : m.Center) (i : Fin 4) :
    (m.officialNodeDescriptorUnitSources demoDetection.initialEnvironment
      (demoDetection.descriptorSourceBranchPolicyWith m DescriptorSourcePolicyProfile.exactDistance)
      center i [OfficialCIPNode.auxiliary (V := Fin 4) 99]).length = 0 := by
  rfl

example (m : OneCenter.MultiCenterMolecule (Fin 4)) (center : m.Center) (i : Fin 4) :
    (m.officialNodeDescriptorUnitSources demoDetection.initialEnvironment
      (demoDetection.descriptorSourceBranchPolicyWith m DescriptorSourcePolicyProfile.kindFallback)
      center i [OfficialCIPNode.auxiliary (V := Fin 4) 99]).length = 1 := by
  rfl

example (m : OneCenter.MultiCenterMolecule (Fin 4)) (center : m.Center) (i : Fin 4) :
    (m.officialNodeDescriptorUnitSources demoDetection.initialEnvironment
      (demoDetection.descriptorSourceBranchPolicyWith m
        { DescriptorSourcePolicyProfile.exactDistance with auxiliarySources := false })
      center i [OfficialCIPNode.auxiliary (V := Fin 4) 0]).length = 0 := by
  rfl

example :
    demoUnit0 ∈ demoDetection.unitsAtAtomBySupport (1 : Fin 4) := by
  rw [demoDetection.mem_unitsAtAtomBySupport_iff]
  simp [demoUnit0, demoDetection, demoBundle, OfficialNoncenterDetectorBundle.toDetectionResult,
    OfficialNoncenterDetectorBundle.detectedUnits, OfficialUnitDetectionResult.unitAt,
    OfficialDetectedUnit.ofDoubleBond]

example :
    (demoDetection.unitsAtAtomBySupport (1 : Fin 4)).length = 4 := by
  rfl

noncomputable def firstDetectedRule3? (result : ChemistryNormalizationResult) :
    Option OfficialRule3Geometry :=
  let detection := result.officialUnitDetectionResult
  match h : detection.units with
  | [] => none
  | _ :: _ =>
      detection.initialEnvironment.rule3Geometry
        (⟨0, by simp [h]⟩ : detection.Unit)

example :
    (result : ChemistryNormalizationResult) →
      result.officialUnitDetectionResult.units =
        result.officialNoncenterDetectorBundle.detectedUnits := by
  intro result
  rfl

example :
    (match parseAndNormalizeOpenSMILES "C=C=C" with
      | Except.ok result => result.detectedCumuleneRecords.length = 1
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseAndNormalizeOpenSMILES "C=C=C" with
      | Except.ok result =>
          match result.detectedCumuleneRecords.head? with
          | some unit => unit.path.map Fin.val == [0, 1, 2]
          | none => false
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseAndNormalizeOpenSMILES "C=C=C" with
      | Except.ok result => result.officialNoncenterDetectorBundle.cumulenes.length = 1
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseAndNormalizeOpenSMILES "C=C=C" with
      | Except.ok result =>
          result.officialNoncenterDetectorBundle.axisCandidates.length == 1
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseAndNormalizeOpenSMILES "c1ccccc1"
        [{ atoms := [0, 1, 2, 3, 4, 5] }] with
      | Except.ok result =>
          result.officialNoncenterDetectorBundle.planeCandidates.length == 1
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseAndNormalizeOpenSMILES "CCCC" with
      | Except.ok result =>
          result.officialNoncenterDetectorBundle.conformationCandidates.length == 3
      | Except.error _ => false) = true := by
  rfl

example :
    (({ axisCandidates :=
          [{ axisStart := (0 : Fin 3), axisEnd := 2, support := [0, 1, 2].toFinset }] } :
        OfficialNoncenterDetectorBundle (Fin 3)).coverage.axes) = 1 := by
  rfl

example :
    (({ planeCandidates := [{ planeAtoms := [(0 : Fin 6), 1, 2, 3, 4, 5] }] } :
        OfficialNoncenterDetectorBundle (Fin 6)).coverage.planes) = 1 := by
  rfl

example :
    (({ conformationCandidates :=
          [{ support := [(0 : Fin 2), 1].toFinset, kind? := none }] } :
        OfficialNoncenterDetectorBundle (Fin 2)).coverage.conformations) = 1 := by
  rfl

example :
    (({ axisCandidates :=
          [{ axisStart := (0 : Fin 3), axisEnd := 2, support := [0, 1, 2].toFinset }] } :
        OfficialNoncenterDetectorBundle (Fin 3)).detectedUnits.head?.map
          OfficialDetectedUnit.hasInitialValue) = some false := by
  rfl

example :
    (({ cumulenes := [{ path := [(0 : Fin 3), 1, 2], stereo? := none }] } :
        OfficialNoncenterDetectorBundle (Fin 3)).detectedUnits.head?.map
          (fun unit => unit.kind)) =
      some OfficialStereochemicalUnitKind.alkeneOrCumulene := by
  rfl

example :
    (match (({ cumulenes := [{ path := [(0 : Fin 3), 1, 2], stereo? := none }] } :
        OfficialNoncenterDetectorBundle (Fin 3)).detectedUnits.head?) with
      | some unit => (0 : Fin 3) ∈ unit.support ∧ (1 : Fin 3) ∈ unit.support ∧
          (2 : Fin 3) ∈ unit.support
      | none => False) := by
  simp [OfficialNoncenterDetectorBundle.detectedUnits, OfficialDetectedUnit.ofCumulenePath]

/-- `C/C=C\C` is cis-2-butene, so its detected double-bond unit carries `Z`. -/
example :
    (match parseAndNormalizeOpenSMILES "C/C=C\\C" with
      | Except.ok result =>
          result.officialNoncenterDetectorBundle.doubleBonds.length == 1 &&
            match result.officialNoncenterDetectorBundle.doubleBonds.head? with
            | some unit => unit.stereo? == some DoubleBondStereo.Z
            | none => false
      | Except.error _ => false) = true := by
  rfl

/-- The same cis double bond seeds the official Rule-3 environment with `seqcis`. -/
example :
    (match parseAndNormalizeOpenSMILES "C/C=C\\C" with
      | Except.ok result =>
          match result.detectedDoubleBondUnits.head? with
          | some unit =>
              match unit.initialValues.head? with
              | some (OfficialDescriptorValue.rule3Geometry OfficialRule3Geometry.seqcis) => true
              | _ => false
          | none => false
      | Except.error _ => false) = true := by
  rfl

/-- The trans spelling seeds `seqtrans`, so the Rule-3 seed tracks the perceived geometry rather
than the raw slash characters. -/
example :
    (match parseAndNormalizeOpenSMILES "C/C=C/C" with
      | Except.ok result =>
          match result.detectedDoubleBondUnits.head? with
          | some unit =>
              match unit.initialValues.head? with
              | some (OfficialDescriptorValue.rule3Geometry OfficialRule3Geometry.seqtrans) => true
              | _ => false
          | none => false
      | Except.error _ => false) = true := by
  rfl

def broadIndexedAnnotations : IndexedNoncenterStereoAnnotations where
  axes :=
    [{ axisStart := 0
       axisEnd := 1
       startHigh := 2
       startLow := 3
       endHigh := 4
       endLow := 5
       descriptor := AxialDescriptor.Sa }]
  planes :=
    [{ planeAtoms := [0, 1, 2]
       pilotAtom := 3
       highReference := 4
       lowReference := 5
       descriptor := PlanarDescriptor.Sp }]
  helices :=
    [{ helixPath := [0, 2, 4]
       frontReference := 1
       backReference := 5
       descriptor := HelicalDescriptor.M }]
  conformations :=
    [{ support := [0, 1, 2, 3, 4, 5]
       kind? := some OfficialStereogenicUnitKind.chiral }]
  ensembles :=
    [{ support := [0, 1, 2, 3, 4, 5]
       kind? := some OfficialStereogenicUnitKind.chiral }]
  auxiliaryRule5Nodes :=
    [{ anchor := 4
       support := [4]
       descriptor := OfficialRule5Descriptor.descriptorR
       rootDistance? := some 1 }]
  phantomNodes :=
    [{ anchor := 5
       support := [5]
       rootDistance? := some 2 }]
  lonePairNodes :=
    [{ anchor := 3
       support := [3]
       rootDistance? := some 3 }]

example :
    (match parseAndNormalizeOpenSMILES "CCCCCC" with
      | Except.ok result =>
          let bundle := result.officialNoncenterDetectorBundleWith broadIndexedAnnotations
          bundle.axes.length == 1 && bundle.planes.length == 1 && bundle.helices.length == 1 &&
            bundle.conformations.length == 1 && bundle.ensembles.length == 1 &&
            bundle.auxiliaryRule5Nodes.length == 1 && bundle.phantomNodes.length == 1 &&
            bundle.lonePairNodes.length == 1
      | Except.error _ => false) = true := by
  rfl

example :
    (match parseAndNormalizeOpenSMILES "CC" with
      | Except.ok result =>
          let badAnnotations : IndexedNoncenterStereoAnnotations :=
            { axes :=
                [{ axisStart := 0
                   axisEnd := 1
                   startHigh := 2
                   startLow := 0
                   endHigh := 1
                   endLow := 0
                   descriptor := AxialDescriptor.Ra }] }
          (result.officialNoncenterDetectorBundleWith badAnnotations).axes.length == 0
      | Except.error _ => false) = true := by
  rfl

example
    {V Unit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Unit]
    (m : OneCenter.MultiCenterMolecule V) (output : OfficialDetectorOutput Unit)
    (policy : BranchFrontierUnitPolicy m Unit) {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel) (center : m.Center) (i : Fin 4) :
    m.officialBranchContextFromFrontierDetectorWithin output policy
        (scheduleFuel + 1) branchFuel center i =
      m.officialBranchContextFromFrontierDetectorWithin output policy
        scheduleFuel branchFuel center i := by
  exact m.officialBranchContextFromFrontierDetectorWithin_succ_eq_of_fixedAt output policy
    branchFuel h center i

example
    {V Unit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Unit]
    (m : OneCenter.MultiCenterMolecule V) (output : OfficialDetectorOutput Unit)
    (policy : DescriptorSourceBranchPolicy m Unit) {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel) (center : m.Center) (i : Fin 4) :
    m.officialBranchContextFromDescriptorSourceDetectorWithin output policy
        (scheduleFuel + 1) branchFuel center i =
      m.officialBranchContextFromDescriptorSourceDetectorWithin output policy
        scheduleFuel branchFuel center i := by
  exact m.officialBranchContextFromDescriptorSourceDetectorWithin_succ_eq_of_fixedAt output policy
    branchFuel h center i

end OfficialNoncenterDetectors
end Examples
end TetraStereo
