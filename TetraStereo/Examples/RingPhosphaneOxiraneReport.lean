import TetraStereo.Examples.RingPhosphaneOxiranePriority

/-! Exact public rows outside the root carbon and reduction of its local
publication to the independently computed phosphorus determinants. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingGroupedReport (origin)
open RingFrameTransport (publishG)
open RingWrittenPHReadings (geometry inputGeometry_eq)
open RingSpatialTransport
open Representatives (hand)
open private c4Center from TetraStereo.Examples.RingPhosphaneOxirane

private theorem root_state (i : Input) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i a = RingChemicalGraphProof.state i (origin i a) :=
  RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a

/-- Actual root publication on a new coordinate table uses the original graph's
local rule with the complete frozen reader computed from the two determinants. -/
theorem c0_local_at_geometry (i : Input) (raw : i.molecule = molecule)
    (x : SpatialConfiguration) (full : x.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x full) = true) :
    RingChemicalGraphProof.root (atGeometry i x full) (atom i raw 0) =
      publishG i (geometry x) (origin i (atom i raw 0))
        (canonicalReader i raw (hand x [5,6,0,1]) (hand x [7,8,0,2])) := by
  let j := atGeometry i x full
  let q := origin j (atom i raw 0)
  have actual := frozen_c0 j raw valid
  have read := RingFrameTransport.publishG_input valid (RingChemicalGraphProof.ready valid q)
  rw [inputGeometry_eq] at actual read
  rw [root_state,RingChemicalGraphProof.state_eq,←read]
  change publishG j (geometry x) q _ = _
  rw [show RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state j) q =
    canonicalReader j raw (hand x [5,6,0,1]) (hand x [7,8,0,2]) from actual]
  rw [show q = reindexSite i x full (origin i (atom i raw 0)) from (reindex_origin i x full _).symm]
  apply publish_reindex
  intro u
  rfl

/-- All non-C0 rows have a closed physical formula at every admitted geometry. -/
theorem peripheral_root (i : Input) (raw : i.molecule = molecule)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) (c : RS) (a : i.certified.Atom)
    (away : a ≠ atom i raw 0) :
    RingChemicalGraphProof.root i a =
      some (labels c (hand i.spatial [5,6,0,1]) (hand i.spatial [7,8,0,2]) a.val) := by
  by_cases first : a = atom i raw 1
  · subst a
    rw [root_state]
    simpa only [inputGeometry_eq] using p1_state i raw valid (origin i (atom i raw 1)) rfl rfl
  by_cases second : a = atom i raw 2
  · subst a
    rw [root_state]
    simpa only [inputGeometry_eq] using p2_state i raw valid (origin i (atom i raw 2)) rfl rfl
  have absent : labels c (hand i.spatial [5,6,0,1]) (hand i.spatial [7,8,0,2]) a.val = none := by
    have nz : a.val ≠ 0 := fun h => away (Fin.ext h)
    have n1 : a.val ≠ 1 := fun h => first (Fin.ext h)
    have n2 : a.val ≠ 2 := fun h => second (Fin.ext h)
    cases h : a.val with
    | zero => contradiction
    | succ n => cases n with
      | zero => contradiction
      | succ n => cases n with
        | zero => contradiction
        | succ => rfl
  rw [absent]
  by_cases four : a = atom i raw 4
  · subst a
    exact (pairAtFour i raw (c4Center i raw) rfl).root_refusal valid
  · have inactive : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (origin i a) := by
      rintro ⟨_,b,current,eligible⟩
      have eqn : a = b := Option.some.inj current
      subst b
      rcases (eligible_ids i raw a).mp eligible with h | h | h | h <;> contradiction
    rw [root_state,RingChemicalGraphProof.state_eq]
    exact RingChemicalGraphProof.skips i _ _ inactive

/-- Equal phosphorus determinants give a full raw report for every valid request,
including the flat-flat case. Other combinations are covered for lists omitting C0. -/
theorem public_rows_of_equal_or_omitted (i : Input) (raw : i.molecule = molecule)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : RS) (ids : List Nat) (bounds : ∀ n ∈ ids, n < 11)
    (condition : hand i.spatial [5,6,0,1] = hand i.spatial [7,8,0,2] ∨ 0 ∉ ids) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids =
      some (ids.map fun n => (n,labels c (hand i.spatial [5,6,0,1]) (hand i.spatial [7,8,0,2]) n)) := by
  rw [←raw]
  apply raw_of_root_labels i _ (raw ▸ closed) valid ids (raw ▸ bounds)
  intro a mem
  by_cases atZero : a = atom i raw 0
  · subst a
    have eqn := condition.resolve_right (fun off => off mem)
    have refused := native_root_refusal i raw valid eqn
    rw [atom_val]
    change RingChemicalGraphProof.root i _ = some (rootLabels c _ _)
    rw [eqn]
    cases hand i.spatial [7,8,0,2] <;> simpa [rootLabels] using refused
  · exact peripheral_root i raw valid c a atZero

/-- For unequal arms the sole remaining chemical decision is a single carbon
publication on the fixed graph. All phosphorus, other atom and request rows follow. -/
theorem raw_of_c0_publication (i : Input) (raw : i.molecule = molecule)
    (x : SpatialConfiguration) (full : x.positions.length = size i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x full) = true)
    (c : RS) (l r : Option RS) (left : hand x [5,6,0,1] = l) (right : hand x [7,8,0,2] = r)
    (localResult : publishG i (geometry x) (origin i (atom i raw 0)) (canonicalReader i raw l r) =
      some (rootLabels c l r)) (ids : List Nat) (bounds : ∀ n ∈ ids, n < 11) :
    RingHydrogenReport.fromRaw? molecule x ids = some (ids.map fun n => (n,labels c l r n)) := by
  let j := atGeometry i x full
  have jraw : j.molecule = molecule := raw
  have root := c0_local_at_geometry i raw x full valid
  rw [left,right,localResult] at root
  change RingHydrogenReport.fromRaw? molecule j.spatial ids = _
  rw [←jraw]
  apply raw_of_root_labels j (labels c l r) (jraw ▸ closed) valid ids (jraw ▸ bounds)
  intro a _
  by_cases zero : a = atom j jraw 0
  · subst a
    exact root
  · have other := peripheral_root j jraw valid c a zero
    change RingChemicalGraphProof.root j a = some (labels c (hand x _) (hand x _) a.val) at other
    rwa [left,right] at other

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.c0_local_at_geometry
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.public_rows_of_equal_or_omitted

assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.raw_of_c0_publication

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingNumberedHydrogenGeometry RingWrittenPHReadings
open Representatives (hand)

/-- Exchanging both phosphorus arms reverses the written carbon determinant. -/
theorem c0_moved (i : Input) (raw : i.molecule = molecule) :
    hand (reindexed i i (branchAutomorphism i raw).atoms) [1,2,3,4] =
      (hand i.spatial [1,2,3,4]).map RS.swap := by
  let g := branchAutomorphism i raw
  have pulled (n : IDs) : geometry (reindexed i i g.atoms) n.val =
      geometry i.spatial (branchPermutation.symm n).val := by
    change (reindexed i i g.atoms).positions[(atom i raw n).val]? = _
    rw [reindexed_lookup,branchAutomorphism_inverse_atom]
    rfl
  have ex : hand (reindexed i i g.atoms) [1,2,3,4] = hand i.spatial [2,1,3,4] := by
    have p1 := pulled 1
    have p2 := pulled 2
    have p3 := pulled 3
    have p4 := pulled 4
    change geometry _ 1 = geometry _ 2 at p1
    change geometry _ 2 = geometry _ 1 at p2
    change geometry _ 3 = geometry _ 3 at p3
    change geometry _ 4 = geometry _ 4 at p4
    simp only [hand,readback?,List.mapM_cons,List.mapM_nil,p1,p2,p3,p4]
  exact ex.trans (LocalizedMarkedTerminalGaugeSwap.readback_swapAtom _ 1 2 (by decide) [1,2,3,4]
    (by decide) rfl (by decide) (by decide))

def RootCase (l r : Option RS) : Prop := ∀ (i : Input) (raw : i.molecule = molecule),
  LocalizedChemicalRing.coordinatesAdmitted i = true → ∀ c : RS,
  hand i.spatial [1,2,3,4] = some c → hand i.spatial [5,6,0,1] = l →
  hand i.spatial [7,8,0,2] = r → RingChemicalGraphProof.root i (atom i raw 0) = some (rootLabels c l r)

private theorem rootLabels_swap (c : RS) (l r : Option RS) :
    rootLabels c.swap r l = rootLabels c l r := by
  cases c <;> cases l with
  | none => cases r with
    | none => rfl
    | some r => cases r <;> rfl
  | some l => cases l <;> cases r with
    | none => rfl
    | some r => cases r <;> rfl

/-- A proof for one order of the two arms covers their reverse order on every
geometry by the actual molecular renumbering of the native root. -/
theorem rootCase_exchange {l r : Option RS} (proved : RootCase l r) : RootCase r l := by
  intro i raw valid c zero left right
  let g := branchAutomorphism i raw
  let j := withSourceGeometry i i g.atoms
  have jraw : j.molecule = molecule := raw
  have ok := g.atSourceGeometry.coordinates valid
  have swapped := c0_moved i raw
  rw [zero] at swapped
  have reevaluated := proved j jraw ok c.swap swapped ((p1_moved i raw).trans right) ((p2_moved i raw).trans left)
  have transported := RingReportRenumber.chemical_root g.atSourceGeometry valid (atom i raw 0)
  have fixed : g.atoms (atom i raw 0) = atom j jraw 0 := branchAutomorphism_atom i raw 0
  change RingChemicalGraphProof.root i _ = RingChemicalGraphProof.root j (g.atoms _) at transported
  rw [fixed,reevaluated,rootLabels_swap] at transported
  exact transported

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.rootCase_exchange

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingWrittenPHReadings (geometry)
open RingSpatialTransport
open Representatives (representative representative_checks hand)
open private reference refRaw refSize from TetraStereo.Examples.RingPhosphaneOxirane

private theorem root_zero_congr {i j : Input} (eqn : i = j)
    (hi : i.molecule = molecule) (hj : j.molecule = molecule) :
    RingChemicalGraphProof.root i (atom i hi 0) = RingChemicalGraphProof.root j (atom j hj 0) := by
  subst j
  rfl

/-- A fixed-graph native publication certificate covers all independently
admitted input tables, including every physical realization of the two arm signs. -/
theorem rootCase_of_local (base : Input) (fixed : base.molecule = molecule) (l r : Option RS)
    (checked : ∀ x : SpatialConfiguration, ∀ c : RS, hand x [1,2,3,4] = some c →
      RingFrameTransport.publishG base (geometry x) (RingGroupedReport.origin base (atom base fixed 0))
        (canonicalReader base fixed l r) = some (rootLabels c l r)) : RootCase l r := by
  intro i raw valid c zero left right
  have graph := fixed.trans raw.symm
  have eqn := eq_atGeometry graph
  let j := atGeometry base i.spatial (full_at_other graph)
  have jraw : j.molecule = molecule := fixed
  have good : LocalizedChemicalRing.coordinatesAdmitted j = true := by
    change LocalizedChemicalRing.coordinatesAdmitted (atGeometry base i.spatial _) = true
    rw [eqn]; exact valid
  have localPub := c0_local_at_geometry base fixed i.spatial (full_at_other graph) good
  rw [left,right,checked _ c zero] at localPub
  exact (root_zero_congr eqn jraw raw).symm.trans localPub

theorem rootCase_equal (l : Option RS) : RootCase l l := by
  intro i raw valid c _ left right
  have noneAtRoot := native_root_refusal i raw valid (left.trans right.symm)
  cases l <;> simpa [rootLabels] using noneAtRoot

theorem public_rows_of_rootCase (i : Input) (raw : i.molecule = molecule)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) (c : RS)
    (zero : hand i.spatial [1,2,3,4] = some c)
    (l r : Option RS) (left : hand i.spatial [5,6,0,1] = l) (right : hand i.spatial [7,8,0,2] = r)
    (proved : RootCase l r) (ids : List Nat) (bounds : ∀ n ∈ ids, n < 11) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = some (ids.map fun n => (n,labels c l r n)) := by
  rw [←raw]
  apply raw_of_root_labels i (labels c l r) (raw ▸ closed) valid ids (raw ▸ bounds)
  intro a _
  by_cases atZero : a = atom i raw 0
  · subst a
    exact proved i raw valid c zero left right
  · simpa only [left,right] using peripheral_root i raw valid c a atZero

/-- Three local priority proofs suffice for every original request on every
rational coordinate table of this molecule. Equal arms and reverse orders derive internally. -/
theorem universal_of_three_cases (opposite : RootCase (some .R) (some .S))
    (leftR : RootCase (some .R) none) (leftS : RootCase (some .S) none) :
    ∀ x ids, RingHydrogenReport.fromRaw? molecule x ids = expectedReport x ids := by
  have casesCover : ∀ l r : Option RS, RootCase l r := by
    intro l r
    cases l with
    | none =>
      cases r with
      | none => exact rootCase_equal none
      | some r => cases r <;> first | exact rootCase_exchange leftR | exact rootCase_exchange leftS
    | some l =>
      cases r with
      | none => cases l <;> assumption
      | some r => cases l <;> cases r <;> first | exact rootCase_equal _ | exact opposite | exact rootCase_exchange opposite
  apply universal_reports_iff.mpr
  intro c l r
  let y := representative c l r
  obtain ⟨len,zero,left,right,four⟩ := representative_checks c l r
  let j := atGeometry reference y (len.trans refSize.symm)
  have raw : j.molecule = molecule := refRaw
  have valid := (coordinates_iff j raw).mpr ⟨by
    change (hand (representative c l r) [1,2,3,4]).isSome = true
    rw [zero]; rfl,four⟩
  exact public_rows_of_rootCase j raw valid c zero l r left right (casesCover l r) _ (fun _ => List.mem_range.mp)

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.rootCase_of_local
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.universal_of_three_cases

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter LocalizedGenericMarkedRecalculation
open RingWrittenPHReadings (geometry)
open Representatives (hand)

/-- With R on P1 and S on P2, the raw evaluator's carbon uses the written
P1, P2, O, C4 orientation and gives the same lowercase descriptor on reflection. -/
theorem opposite_root : RootCase (some .R) (some .S) := by
  apply rootCase_of_local PhosRootKey.reference PhosRootKey.reference_molecule
  intro x c zero
  have publication := PhosRootKey.publish_pseudo (geometry x)
  change readback? (geometry x) [1,2,3,4] = some c at zero
  rw [zero] at publication
  exact publication

/-- Other order of the enantiomorphic arms, including the reversal of C0 priority. -/
theorem opposite_root_reversed : RootCase (some .S) (some .R) := rootCase_exchange opposite_root

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.opposite_root
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.opposite_root_reversed

namespace TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
open OneCenter LocalizedGenericMarkedRecalculation
open RingWrittenPHReadings (geometry)
open Representatives (hand)

theorem one_flat_root (h : RS) : RootCase (some h) none := by
  apply rootCase_of_local PhosRootKey.reference PhosRootKey.reference_molecule
  intro x c zero
  have publication := PhosRootKey.oneFlat_publish h (geometry x)
  change readback? (geometry x) [1,2,3,4] = some c at zero
  rw [zero] at publication
  exact publication

/-- Exact public response for the fully written phosphane-substituted oxirane, on
every rational coordinate table and every original atom request. Both phosphorus
signs and the carbon sign are computed directly from the supplied points. -/
theorem public_exact (x : SpatialConfiguration) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule x ids = expectedReport x ids :=
  universal_of_three_cases opposite_root (one_flat_root .R) (one_flat_root .S) x ids

end TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.one_flat_root
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.PhosphaneOxirane.public_exact
