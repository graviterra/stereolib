import TetraStereo.Examples.DecalinPathSwap
import TetraStereo.Examples.MixedHalogenSpiro

/-! cis/trans-decalin, IUPAC Blue Book P-93.5.4.1. The coordinates and atom order
are from VS211 and VS212 in compounds_3d.sdf at CIPValidationSuite/ValidationSuite
commit 6b9f9db46dadc6749da8234b05164e1e0fb413b9, file SHA-256
28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325.
All coordinates have been multiplied by 10000 exactly. The SDF junction IDs
1 and 2 correspond to public raw IDs 0 and 1. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinPublishedCoordinates
open OneCenter Engine

open DecalinFrames (molecule junctionRow expected independentReport? Representative)

def vs211 : SpatialConfiguration := ⟨[
  ⟨23063,-12280,-1137⟩, ⟨23059,-27931,-1330⟩, ⟨10648,-5513,-7002⟩, ⟨10171,-35138,-6320⟩,
  ⟨-2102,-12963,-3708⟩, ⟨-1722,-26482,-10480⟩, ⟨35478,-5521,-7009⟩, ⟨48225,-12972,-3711⟩,
  ⟨35946,-35144,-6314⟩, ⟨47842,-26494,-10478⟩, ⟨23067,-9565,9538⟩, ⟨23056,-30356,9350⟩,
  ⟨11559,-4728,-17919⟩, ⟨9937,4728,-3276⟩, ⟨6756,-41740,1709⟩, ⟨12351,-41888,-14612⟩,
  ⟨-10702,-7271,-7333⟩, ⟨-3264,-14049,7152⟩, ⟨-11078,-31871,-8465⟩, ⟨-1416,-25013,-21307⟩,
  ⟨36193,4723,-3291⟩, ⟨34566,-4744,-17927⟩, ⟨49386,-14054,7150⟩, ⟨56827,-7284,-7337⟩,
  ⟨33765,-41898,-14602⟩, ⟨39359,-41742,1718⟩, ⟨57196,-31885,-8462⟩, ⟨47535,-25028,-21305⟩]⟩

def vs212 : SpatialConfiguration := ⟨[
  ⟨22974,-8693,-8087⟩, ⟨22992,-18107,-20305⟩, ⟨10399,127,-8103⟩, ⟨10178,-26513,-20816⟩,
  ⟨-2400,-8103,-9011⟩, ⟨-2213,-17566,-20997⟩, ⟨35586,30,-8020⟩, ⟨48349,-8301,-8766⟩,
  ⟨35648,-26774,-20506⟩, ⟨48168,-18057,-20481⟩, ⟨22915,-14743,1049⟩, ⟨23177,-11959,-29360⟩,
  ⟨10757,7074,-16539⟩, ⟨10127,6288,967⟩, ⟨9710,-33258,-12215⟩, ⟨10167,-32843,-29778⟩,
  ⟨-11040,-1376,-9780⟩, ⟨-3720,-13863,172⟩, ⟨-11238,-23710,-20984⟩, ⟨-2375,-11726,-30246⟩,
  ⟨35816,6261,939⟩, ⟨35374,6914,-16578⟩, ⟨49556,-13893,596⟩, ⟨56996,-1682,-9588⟩,
  ⟨35692,-33176,-29356⟩, ⟨35797,-33455,-11780⟩, ⟨57108,-24391,-20154⟩, ⟨48695,-12421,-29897⟩]⟩


open TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
open private coordinates_of_neighbor_volumes from TetraStereo.Examples.MixedHalogenSpiro
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_hands :
    readback? (RingWrittenPHReadings.geometry vs211) (junctionRow 0) = some .S ∧
    readback? (RingWrittenPHReadings.geometry vs211) (junctionRow 1) = some .R ∧
    readback? (RingWrittenPHReadings.geometry vs212) (junctionRow 0) = some .S ∧
    readback? (RingWrittenPHReadings.geometry vs212) (junctionRow 1) = some .S := by decide +kernel
private def input211 := (LocalizedChemicalRing.admitRawSpatial? molecule vs211).get (by decide +kernel)
private def input212 := (LocalizedChemicalRing.admitRawSpatial? molecule vs212).get (by decide +kernel)
theorem source_admitted : LocalizedChemicalRing.coordinatesAdmitted input211 = true ∧
    LocalizedChemicalRing.coordinatesAdmitted input212 = true :=
  ⟨coordinates_of_neighbor_volumes _ (by decide +kernel), coordinates_of_neighbor_volumes _ (by decide +kernel)⟩

/-- Admission and determinant calibration of the fixed public coordinates are discharged
above. Only the two displayed computations of the public rows remain as premises. -/
theorem complete_of_sdf_rows
    (cis : RingHydrogenReport.fromRaw? molecule vs211 [0,1] = some (expected .S .R [0,1]))
    (trans : RingHydrogenReport.fromRaw? molecule vs212 [0,1] = some (expected .S .S [0,1]))
    (i : LocalizedChemicalRing.Input) (graph : i.molecule = molecule)
    (admitted : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = independentReport? i.spatial ids := by
  have c : LocalizedChemicalRing.admitRawSpatial? molecule vs211 = some input211 := (Option.some_get _).symm
  have t : LocalizedChemicalRing.admitRawSpatial? molecule vs212 = some input212 := (Option.some_get _).symm
  obtain ⟨cm,cg⟩ := RingChemicalReport.admission_fields c
  obtain ⟨tm,tg⟩ := RingChemicalReport.admission_fields t
  obtain ⟨u,v,w,z⟩ := source_hands
  exact DecalinPathSwap.complete_of_two
    ⟨input211,cm,source_admitted.1,cg ▸ u,cg ▸ v,cg ▸ cis⟩
    ⟨input212,tm,source_admitted.2,tg ▸ w,tg ▸ z,tg ▸ trans⟩ i graph admitted ids

end TetraStereo.Examples.DecalinPublishedCoordinates
assert_kernel_only TetraStereo.Examples.DecalinPublishedCoordinates.source_hands
assert_kernel_only TetraStereo.Examples.DecalinPublishedCoordinates.source_admitted
assert_kernel_only TetraStereo.Examples.DecalinPublishedCoordinates.complete_of_sdf_rows
