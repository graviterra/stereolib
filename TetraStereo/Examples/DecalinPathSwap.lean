import TetraStereo.Examples.DecalinFrames

/-! In decalin, exchanging the two four-carbon routes fixes both fusion atoms
and their hydrogens. Pulling coordinates through this graph automorphism
reverses the two local reference hands and preserves the native junction report. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinPathSwap
open Engine OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open DecalinFrames
open RingNumberedHydrogenGeometry (withSourceGeometry reindexed_lookup)
open RingRawRenumbering (AtomMap)

def exchange : Nat → Nat
  | 2 => 6 | 6 => 2 | 4 => 7 | 7 => 4 | 5 => 9 | 9 => 5 | 3 => 8 | 8 => 3
  | 12 => 20 | 20 => 12 | 13 => 21 | 21 => 13 | 16 => 22 | 22 => 16
  | 17 => 23 | 23 => 17 | 18 => 26 | 26 => 18 | 19 => 27 | 27 => 19
  | 14 => 24 | 24 => 14 | 15 => 25 | 25 => 15 | n => n

private theorem eq_size (i : Input) (raw : i.molecule = molecule) : RingSpatialTransport.size i = 28 := by
  rw [RingSpatialTransport.size,i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,raw]; rfl

private theorem graph : ∀ a : Fin 28, exchange a.val < 28 ∧ exchange (exchange a.val) = a.val ∧
    molecule.atoms[exchange a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : Fin 28, molecule.bondOrder (exchange a.val) (exchange b.val) = molecule.bondOrder a.val b.val := by
  decide +kernel

private def index (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) : Fin 28 :=
  ⟨a.val,by rw [←eq_size i raw]; exact a.isLt⟩

private def perm (i : Input) (raw : i.molecule = molecule) : Equiv.Perm i.certified.Atom :=
  let f (a : i.certified.Atom) : i.certified.Atom := ⟨exchange a.val,by
    change exchange a.val < RingSpatialTransport.size i
    rw [eq_size i raw]
    exact (graph (index i raw a)).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (graph (index i raw a)).2.1
  ⟨f,f,inv,inv⟩

def transported (i : Input) (raw : i.molecule = molecule) : Input := withSourceGeometry i i (perm i raw)

private def atomMap (i : Input) (raw : i.molecule = molecule) : AtomMap i (transported i raw) where
  atoms := perm i raw
  records a := by
    change (i.molecule.atoms[exchange a.val]?).map _ = _
    rw [raw]
    exact congrArg (Option.map _) (graph (index i raw a)).2.2.1
  bonds a b := by
    change i.molecule.bondOrder (exchange a.val) (exchange b.val) = _
    rw [raw]
    exact (graph (index i raw a)).2.2.2 (index i raw b)
  positions a := RingNumberedHydrogenGeometry.reindexed_lookup_image _ _

private theorem point (i : Input) (raw : i.molecule = molecule) (n : Nat) (hn : n < 28) :
    RingWrittenPHReadings.geometry (transported i raw).spatial n =
      RingWrittenPHReadings.geometry i.spatial (exchange n) := by
  let a : i.certified.Atom := ⟨n,by change n < RingSpatialTransport.size i; rwa [eq_size i raw]⟩
  exact reindexed_lookup (perm i raw) a

private theorem swap_middle (g : Geometry) (a b c d : Nat) :
    readback? g [a,c,b,d] = (readback? g [a,b,c,d]).map RS.swap := by
  have neg (A B C D : CartesianPoint3) : CartesianPoint3.orientedVolume A C B D =
      -CartesianPoint3.orientedVolume A B C D := by simp only [CartesianPoint3.orientedVolume]; ring
  simp only [readback?,List.mapM_cons,List.mapM_nil]
  cases g a <;> cases g b <;> cases g c <;> cases g d <;>
    first | rfl | (change descriptorOfOrientedVolume? (CartesianPoint3.orientedVolume _ _ _ _) = _
                   rw [neg,descriptorOfOrientedVolume?_neg]; rfl)

theorem swaps_reading (i : Input) (raw : i.molecule = molecule) (j : Fin 2) :
    readback? (RingWrittenPHReadings.geometry (transported i raw).spatial) (junctionRow j.val) =
      (readback? (RingWrittenPHReadings.geometry i.spatial) (junctionRow j.val)).map RS.swap := by
  fin_cases j
  · refine Eq.trans ?_ (swap_middle _ 1 2 6 10)
    change readback? _ [1,2,6,10] = readback? _ [1,6,2,10]
    simp only [readback?,List.mapM_cons,List.mapM_nil]
    simp only [point i raw _ (by decide : 1 < 28),point i raw _ (by decide : 2 < 28),
      point i raw _ (by decide : 6 < 28),point i raw _ (by decide : 10 < 28)]
    rfl
  · refine Eq.trans ?_ (swap_middle _ 0 3 8 11)
    change readback? _ [0,3,8,11] = readback? _ [0,8,3,11]
    simp only [readback?,List.mapM_cons,List.mapM_nil,point i raw _ (by decide : 0 < 28),
      point i raw _ (by decide : 3 < 28),point i raw _ (by decide : 8 < 28),
      point i raw _ (by decide : 11 < 28)]
    rfl

private theorem rename_fixed (i : Input) (raw : i.molecule = molecule) (n : Nat) (h : exchange n = n) :
    RingReportRenumber.renameId (atomMap i raw) n = n := by
  unfold RingReportRenumber.renameId
  split
  · exact h
  · rfl

def swapRepresentative {a b : RS} (r : Representative a b) : Representative a.swap b.swap where
  input := transported r.input r.raw
  raw := r.raw
  admitted := (atomMap r.input r.raw).coordinates r.admitted
  first := (swaps_reading r.input r.raw 0).trans (congrArg (Option.map RS.swap) r.first)
  second := (swaps_reading r.input r.raw 1).trans (congrArg (Option.map RS.swap) r.second)
  checked := by
    let m := atomMap r.input r.raw
    have z : RingReportRenumber.renameId m 0 = 0 := rename_fixed _ _ _ rfl
    have o : RingReportRenumber.renameId m 1 = 1 := rename_fixed _ _ _ rfl
    have result := RingReportRenumber.closed_raw_report m (r.raw ▸ closed) (r.raw ▸ closed) [0,1]
    change RingHydrogenReport.fromRaw? r.input.molecule (transported r.input r.raw).spatial
      ([0,1].map (RingReportRenumber.renameId m)) =
      (RingHydrogenReport.fromRaw? r.input.molecule r.input.spatial [0,1]).map _ at result
    simp only [List.map_cons,List.map_nil,z,o,r.raw,r.checked] at result
    rw [result]
    have eq (n : Nat) (l : Option RingNestedActivePair.Labels) :
        m.renameRow (n,l) = (RingReportRenumber.renameId m n,l) := rfl
    cases a <;> cases b <;> simp [expected,eq,z,o,fusionLabel,RS.swap]

/-- VS211 has local signs S,R and VS212 S,S; exchanging the two equivalent
paths constructs the other representatives without a further public evaluation. -/
theorem complete_of_two (cis : Representative .S .R) (trans : Representative .S .S)
    (i : Input) (raw : i.molecule = molecule) (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = independentReport? i.spatial ids := by
  apply raw_complete_of_representatives _ i raw admit ids
  intro a b
  cases a <;> cases b
  · exact swapRepresentative trans
  · exact swapRepresentative cis
  · exact cis
  · exact trans
/-- A computation of the two fusion rows together with its equality to the
native API at exactly the same graph, coordinates and ordered request. -/
structure JunctionReader where
  read : SpatialConfiguration → Option RingGroupedReport.Report
  exact_read (g : SpatialConfiguration) :
    read g = RingHydrogenReport.fromRaw? molecule g [0,1]

def nativeReader : JunctionReader where
  read g := RingHydrogenReport.fromRaw? molecule g [0,1]
  exact_read _ := rfl

/-- Successful evaluation constructs a representative from this very coordinate
table. Admission, ordered determinants, and the actual fusion rows are checked. -/
def checkWith (reader : JunctionReader) (g : SpatialConfiguration) (a b : RS) :
    Option (Representative a b) :=
  match found : LocalizedChemicalRing.admitRawSpatial? molecule g with
  | none => none
  | some i =>
    if ok : LocalizedChemicalRing.coordinatesAdmitted i = true ∧
        readback? (RingWrittenPHReadings.geometry g) (junctionRow 0) = some a ∧
        readback? (RingWrittenPHReadings.geometry g) (junctionRow 1) = some b ∧
        reader.read g = some (expected a b [0,1]) then
      let fields := RingChemicalReport.admission_fields found
      some {
        input := i, raw := fields.1, admitted := ok.1
        first := fields.2 ▸ ok.2.1, second := fields.2 ▸ ok.2.2.1
        checked := fields.2 ▸ (reader.exact_read g).symm.trans ok.2.2.2 }
    else none

abbrev check := checkWith nativeReader

/-- The same two successful calls which produce witnesses discharge the two
computational premises of the domain theorem. Their coordinate tables can be
chosen independently, as can the verified implementations used for them. -/
theorem complete_of_checks (left right : JunctionReader) (cis trans : SpatialConfiguration)
    (cis_ok : (checkWith left cis .S .R).isSome = true)
    (trans_ok : (checkWith right trans .S .S).isSome = true)
    (i : Input) (raw : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = independentReport? i.spatial ids :=
  complete_of_two ((checkWith left cis .S .R).get cis_ok) ((checkWith right trans .S .S).get trans_ok)
    i raw admit ids

theorem complete_of_native_checks (cis trans : SpatialConfiguration)
    (cis_ok : (check cis .S .R).isSome = true) (trans_ok : (check trans .S .S).isSome = true)
    (i : Input) (raw : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = independentReport? i.spatial ids :=
  complete_of_checks nativeReader nativeReader cis trans cis_ok trans_ok i raw admit ids

end TetraStereo.Examples.DecalinPathSwap
assert_kernel_only TetraStereo.Examples.DecalinPathSwap.complete_of_two
assert_kernel_only TetraStereo.Examples.DecalinPathSwap.complete_of_native_checks
