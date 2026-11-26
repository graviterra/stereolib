import TetraStereo.Engine.RingOriginOrderRanks
import TetraStereo.Engine.RingOriginOrderTransport
import TetraStereo.Engine.RingOriginCausal

/-! At a scheduled auxiliary, check distances between actual closure origins
using just the rooted occurrence histories. Equal depth must give equal
distance, as well as both strict orders agreeing. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginOrderDomain
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingSingleCycleOrigin (originPath pathDistance)
open RingSingleCycleComparison (weight native active)
open RingRetainedChemicalTrace (Observation)
open private observed from TetraStereo.Engine.RingTerminalLigandOrder

def distance {i : Input} (f : Site i) (q : Arm i) (d : Nat) :=
  pathDistance f.val.node.history.reverse (originPath q.occurrence.val.node d)

def Closure {i : Input} (f : Site i) (q : Arm i) (d : Nat) : Prop :=
  q.occurrence.val.root = f.val.root ∧ q.occurrence.val.node.provenance = .ringDuplicate d

def PreservesOrder {i : Input} (f : Site i) : Prop :=
  ∀ (q p : Arm i) (d e : Nat), Closure f q d → Closure f p e →
    (d < e ↔ distance f q d < distance f p e)

private theorem real_length {i : Input} (f : Site i) (real : f.val.node.provenance = .realAtom) :
    f.val.node.history.length ≤ i.molecule.atomCount := by
  have simple := i.certified.simpleOccurrencePath_of_carrier_real i.single f real
  rw [← i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]
  simpa using (i.certified.simpleOccurrencePath_history_nodup simple).length_le_card

private theorem bounds {i : Input} (f : Site i) (real : f.val.node.provenance = .realAtom)
    {q : Arm i} {d : Nat} (c : Closure f q d) :
    d ≤ i.molecule.atomCount ∧ distance f q d ≤ 2*i.molecule.atomCount := by
  obtain ⟨s,_,sr,hist,len⟩ := RingOriginSeparation.origin_real q.occurrence c.2
  have sf := real_length f real
  have so := real_length s sr
  have ol : (originPath q.occurrence.val.node d).length = s.val.node.history.length := by
    rw [←hist,List.length_reverse]
  unfold distance pathDistance
  simp only [List.length_reverse,ol]
  omega

/-- Include real nodes as the lowest class. A genuine closure always has
positive scores on both scales. -/
private def Pair {i : Input} (f : Site i) (x y : Nat) : Prop :=
  (x = 0 ∧ y = 0) ∨ ∃ (q : Arm i) (d : Nat), Closure f q d ∧
    x = i.molecule.atomCount + 1 - d ∧ y = 1 + (2*i.molecule.atomCount - distance f q d)

theorem factors {i : Input} (f : Site i) (real : f.val.node.provenance = .realAtom)
    (order : PreservesOrder f) : RingOriginOrderTransport.Observations i f := by
  have bound (x y : Nat) (p : Pair f x y) : x ≤ i.molecule.atomCount+1 := by
    rcases p with ⟨rfl,_⟩ | ⟨_,_,_,rfl,_⟩ <;> omega
  have monotone (x y u v : Nat) (p : Pair f x y) (t : Pair f u v) : x < u ↔ y < v := by
    rcases p with ⟨rfl,rfl⟩ | ⟨q,d,c,rfl,rfl⟩ <;> rcases t with ⟨rfl,rfl⟩ | ⟨z,e,b,rfl,rfl⟩
    · rfl
    · have := bounds f real b; omega
    · omega
    · have := bounds f real c
      have := bounds f real b
      have := order z q e d b c
      omega
  obtain ⟨rank,g,h,hg,hh,decode⟩ := RingOriginOrderRanks.compress (Pair f) _ bound monotone
  refine ⟨fun q => (native i q).map (RingDuplicateScale.observation rank),g,h,hg,hh,?_⟩
  intro q on
  cases hit : native i q with
  | none => simp [active,hit]
  | some o =>
    rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single q.occurrence with r | ⟨d,dup⟩
    · have zero := (RingRetainedChemicalTrace.real_source r hit).1
      obtain ⟨gx,hx⟩ := decode _ _ (Or.inl ⟨zero,rfl⟩ : Pair f o.duplicate 0)
      cases o
      simp_all [active,RingDuplicateScale.observation]
    · have val := (observed hit).1
      rw [dup] at val
      obtain ⟨gx,hx⟩ := decode _ _ (Or.inr ⟨q,d,⟨on,dup⟩,val,rfl⟩ : Pair f o.duplicate _)
      cases o
      simp_all [active,RingDuplicateScale.observation,weight,distance]

/-- The test uses only closure pairs at scheduled non-root sites, independently
of prior descriptors, atom priorities, sorting and the eventual report. -/
def Qualifies (i : Input) (r : i.certified.Atom) : Prop :=
  ∀ f, RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f → PreservesOrder f

theorem queued {i : Input} {r : i.certified.Atom} (ok : Qualifies i r) :
    RingOriginOrderTransport.Queued i r := by
  intro batch f h
  have cand := ((RingEligibleGraph.inventory i _ r batch f).mp h).1
  exact factors f cand.2.2.1 (ok f cand)

theorem rows_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r : i.certified.Atom} (ok : Qualifies i r) (batches : Nat) :
    RingOriginMetricReport.rows i r batches = RingSphereStore.rows i r batches :=
  RingOriginOrderTransport.rows_exact geom r (queued ok) batches

theorem raw_exact (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (ok : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms → ∀ r ∈ atoms, Qualifies i r) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  RingOriginOrderTransport.raw_exact m g ids (fun i atoms reached r mem => queued (ok i atoms reached r mem))

/-- A changed raw answer needs a pair of measured closure origins at the
very auxiliary where changing the policy affects the recomputed root. -/
theorem raw_witness {m : RawMolecule} {g : SpatialConfiguration} {ids : List Nat}
    (diff : RingOriginMetricReport.fromRaw? m g ids ≠ RingHydrogenReport.fromRaw? m g ids) :
    ∃ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms ∧ ∃ r ∈ atoms,
      ∃ before f after, RingOriginCausal.Switch r f before after ∧
        ∃ q p d e, Closure f q d ∧ Closure f p e ∧
          compare d e ≠ compare (distance f q d) (distance f p e) := by
  classical
  obtain ⟨i,atoms,reached,r,mem,_,_,before,f,after,sw⟩ := RingOriginCausal.raw_switch diff
  refine ⟨i,atoms,reached,r,mem,before,f,after,sw,?_⟩
  by_contra! agrees
  have ok : PreservesOrder f := by
    intro q p d e x y
    have h := agrees q p d e x y
    exact ⟨fun lt => compare_lt_iff_lt.mp (h ▸ compare_lt_iff_lt.mpr lt),
      fun lt => compare_lt_iff_lt.mp (h.symm ▸ compare_lt_iff_lt.mpr lt)⟩
  obtain ⟨_,_,_,_,localDiff⟩ := sw.localDifference
  exact localDiff (RingOriginOrderTransport.publish_exact reached.admitted f (factors f sw.candidate.2.2.1 ok) _)

end TetraStereo.Engine.RingOriginOrderDomain
assert_kernel_only TetraStereo.Engine.RingOriginOrderDomain.rows_exact
assert_kernel_only TetraStereo.Engine.RingOriginOrderDomain.raw_exact
assert_kernel_only TetraStereo.Engine.RingOriginOrderDomain.raw_witness
