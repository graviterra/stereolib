import TetraStereo.Engine.RingOriginFullKeys

/-! Exhausted ordinary arms retain equal active-origin priorities through all
stereochemical passes when their successful occurrence reads are empty. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTwinLeaves
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingStereoSiblingPass (Branch)
open private nextWith budget from TetraStereo.Engine.RingFullPathPairs
open private edges from TetraStereo.Engine.RingOriginFullKeys
open private children from TetraStereo.Engine.RingRetainedStereoRefinement

private theorem terminal_word {i : Input} (read : Reader i) (rev : Bool)
    (rank : Arm i → Option Branch) (seed : RS) (q : Arm i)
    (leaf : i.certified.executableLocalizedRerootChildren q = [])
    (seen : read q.occurrence = some none) :
    RingFullPathPairs.wordWith read rev i.certified.executableLocalizedRerootChildren rank seed q = some [] := by
  simp [RingFullPathPairs.wordWith,RingFullPathPairs.sphereRun,nextWith,
    RingFullPathPairs.rootVisit,RingFullPathPairs.Oracle.root,leaf,RingStereoSiblingPass.order,
    RingFullPathPairs.likeAt,RingFullPathPairs.handAt,seen,RingNestedActivePair.upper]

/-- Equality is required only at the constitutional lookup of the two leaves;
all cumulative passes and both reference words are derived from it. -/
theorem fullKey_eq {i : Input} (keys : Arm i → Option RingRetainedChemicalTrace.Key)
    (read : Reader i) (rev : Bool) (a b : Arm i)
    (la : i.certified.executableLocalizedRerootChildren a = [])
    (lb : i.certified.executableLocalizedRerootChildren b = [])
    (ra : read a.occurrence = some none) (rb : read b.occurrence = some none)
    (same : keys a = keys b) :
    RingOriginFullKeys.fullKey i read rev (RingOriginStereoRanking.priorityWith i keys read rev) a =
    RingOriginFullKeys.fullKey i read rev (RingOriginStereoRanking.priorityWith i keys read rev) b := by
  have ranks (s : List RingRetainedStereoRefinement.Observation) :
      RingOriginStereoRanking.priorityWith i keys read rev s a =
      RingOriginStereoRanking.priorityWith i keys read rev s b := by
    induction s with
    | nil =>
      simp only [RingOriginStereoRanking.priorityWith,RingOriginStereoRanking.unitWith,la,lb,ra,rb]
      simp [same]
    | cons o s ih =>
      simp only [RingOriginStereoRanking.priorityWith,RingRetainedStereoRefinement.build,children,la,lb,ra,rb]
      simp [ih]
  unfold RingOriginFullKeys.fullKey
  simp only [terminal_word read rev _ _ a la ra,terminal_word read rev _ _ b lb rb,ranks]

/-- Rebuilding a real terminal arm observes only its atomic record. -/
theorem rebuilt_eq {i : Input} (f : Site i) (a b : Arm i)
    (la : i.certified.executableLocalizedRerootChildren a = [])
    (lb : i.certified.executableLocalizedRerootChildren b = [])
    (ar : a.occurrence.val.node.provenance = .realAtom)
    (br : b.occurrence.val.node.provenance = .realAtom)
    (obs : RingSingleCycleComparison.native i a = RingSingleCycleComparison.native i b) :
    RingSingleCycleComparison.rebuilt i f a = RingSingleCycleComparison.rebuilt i f b := by
  simp [RingSingleCycleComparison.rebuilt,RingDuplicateScale.build,
    RingSingleCycleComparison.active,ar,br,la,lb,obs]

/-- Identical molecular records give identical ordinary observations, including
failure of the reviewed isotope-mass lookup. -/
theorem native_eq_of_records {i : Input} (a b : Arm i) (u v : i.certified.Atom)
    (ac : a.occurrence.val.node.current? = some u)
    (bc : b.occurrence.val.node.current? = some v)
    (ar : a.occurrence.val.node.provenance = .realAtom)
    (br : b.occurrence.val.node.provenance = .realAtom)
    (records : (i.molecule.atoms[u.val]?).map RingRawRenumbering.molecularRecord =
      (i.molecule.atoms[v.val]?).map RingRawRenumbering.molecularRecord) :
    RingSingleCycleComparison.native i a = RingSingleCycleComparison.native i b := by
  cases ha : i.molecule.atoms[u.val]? with
  | none =>
    have hb : i.molecule.atoms[v.val]? = none := by
      simpa [ha] using records.symm
    simp [RingSingleCycleComparison.native,RingRetainedChemicalTrace.observation?,ac,bc,ha,hb]
  | some x =>
    cases hb : i.molecule.atoms[v.val]? with
    | none => simp [ha,hb] at records
    | some y =>
      have eqn : RingRawRenumbering.molecularRecord x = RingRawRenumbering.molecularRecord y := by
        simpa [ha,hb] using records
      have element := congrArg RingRawRenumbering.MolecularRecord.element eqn
      have mass := congrArg RingRawRenumbering.MolecularRecord.mass eqn
      simp only [RingRawRenumbering.molecularRecord] at element mass
      rw [element] at mass
      simp [RingSingleCycleComparison.native,RingRetainedChemicalTrace.observation?,ac,bc,ar,br,
        ha,hb,element,mass]

theorem active_eq {i : Input} (f : Site i) (read : Reader i) (rev : Bool) (a b : Arm i)
    (la : i.certified.executableLocalizedRerootChildren a = [])
    (lb : i.certified.executableLocalizedRerootChildren b = [])
    (ra : read a.occurrence = some none) (rb : read b.occurrence = some none)
    (ar : a.occurrence.val.node.provenance = .realAtom)
    (br : b.occurrence.val.node.provenance = .realAtom)
    (obs : RingSingleCycleComparison.native i a = RingSingleCycleComparison.native i b) :
    RingOriginFullKeys.active i f read rev a = RingOriginFullKeys.active i f read rev b :=
  fullKey_eq _ read rev a b la lb ra rb (rebuilt_eq f a b la lb ar br obs)

/-- The two constitutional keys already tie before stereochemical passes. -/
theorem twin_rebuilt_eq {i : Input} (p : RingHydrogenSpelling.TwinPair i)
    (f : Site i) (a b : Arm i)
    (la : i.certified.executableLocalizedRerootChildren a = [])
    (lb : i.certified.executableLocalizedRerootChildren b = [])
    (ac : a.occurrence.val.node.current? = some p.u)
    (bc : b.occurrence.val.node.current? = some p.v)
    (ar : a.occurrence.val.node.provenance = .realAtom)
    (br : b.occurrence.val.node.provenance = .realAtom) :
    RingSingleCycleComparison.rebuilt i f a = RingSingleCycleComparison.rebuilt i f b :=
  rebuilt_eq f a b la lb ar br (native_eq_of_records a b p.u p.v ac bc ar br p.records)

/-- The actual twin records suffice for every active full-key coordinate. -/
theorem twin_active_eq {i : Input} (p : RingHydrogenSpelling.TwinPair i)
    (f : Site i) (read : Reader i) (rev : Bool) (a b : Arm i)
    (la : i.certified.executableLocalizedRerootChildren a = [])
    (lb : i.certified.executableLocalizedRerootChildren b = [])
    (ra : read a.occurrence = some none) (rb : read b.occurrence = some none)
    (ac : a.occurrence.val.node.current? = some p.u)
    (bc : b.occurrence.val.node.current? = some p.v)
    (ar : a.occurrence.val.node.provenance = .realAtom)
    (br : b.occurrence.val.node.provenance = .realAtom) :
    RingOriginFullKeys.active i f read rev a = RingOriginFullKeys.active i f read rev b :=
  active_eq f read rev a b la lb ra rb ar br
    (native_eq_of_records a b p.u p.v ac bc ar br p.records)

end TetraStereo.Engine.RingOriginTwinLeaves
assert_kernel_only TetraStereo.Engine.RingOriginTwinLeaves.active_eq
assert_kernel_only TetraStereo.Engine.RingOriginTwinLeaves.twin_active_eq
assert_kernel_only TetraStereo.Engine.RingOriginTwinLeaves.twin_rebuilt_eq
