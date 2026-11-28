import TetraStereo.Examples.DecalinEarlierTie
import TetraStereo.Engine.RingEqualPathHandCounts
import TetraStereo.Engine.RingSparseTwinReport

/-! Eight molecular graph automorphisms for the 33-atom phosphorus-tip fixture.
They support unsigned comparisons across all tip assignments and signed exchanges
when the two arms have the same distribution of hands beneath their B parents. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace TetraStereo.Examples.ResidualPhosphorusCarrier
open Engine OneCenter CertifiedLocalizedCIPInput
attribute [local instance] lexOrd
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingGroupedReport (origin)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open DecalinAuxiliary (history)
open private site_eq start from TetraStereo.Examples.DecalinEarlierTie
open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
def molecule : RawMolecule :=
  let elements : List Element := [.C,.O,.S] ++ List.replicate 6 .B ++ List.replicate 8 .P ++
    (List.range 8).flatMap (fun _ => [.F,.Cl])
  let scaffold := [(0,1),(1,2),(2,0),(0,3),(0,4),(3,5),(3,6),(4,7),(4,8)]
  let tips := (List.range 8).flatMap (fun k => [(5+k/2,9+k),(9+k,17+2*k),(9+k,18+2*k)])
  { atoms := elements.map AtomSpec.aliphatic
    bonds := (scaffold ++ tips).map fun (a,b) => ⟨a,b,.single⟩ }

/-- Bits 0, 1 and 2 select the parent swap and the two independent
within-parent tip swaps. On the right arm we use the inverse map. -/
private def sideTip (choice : Fin 8) (k : Nat) : Nat :=
  let parent := (k%4)/2
  let target := if choice.val.testBit 0 then 1-parent else parent
  let source := if k < 4 then parent else target
  let pos := if choice.val.testBit (1+source) then 1-k%2 else k%2
  (if k < 4 then 4 else 0) + 2*target + pos

def rename (choice : Fin 8) (a : Nat) : Nat :=
  if a < 3 then a else if a < 5 then 7-a else if a < 9 then
    5 + (sideTip choice (2*(a-5)))/2
  else if a < 17 then 9 + sideTip choice (a-9)
  else if a < 33 then 17 + 2*sideTip choice ((a-17)/2) + (a-17)%2 else a

abbrev exchange := rename 0

private theorem eq_size (i : Input) (raw : i.molecule = molecule) : RingSpatialTransport.size i = 33 := by
  rw [RingSpatialTransport.size,i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,raw]; rfl

private theorem graph (choice : Fin 8) : ∀ a : Fin 33, rename choice a.val < 33 ∧ rename choice (rename choice a.val) = a.val ∧
    molecule.atoms[rename choice a.val]? = molecule.atoms[a.val]? ∧
    ∀ b : Fin 33, molecule.bondOrder (rename choice a.val) (rename choice b.val) = molecule.bondOrder a.val b.val := by
  fin_cases choice <;> decide +kernel

private def index (i : Input) (raw : i.molecule = molecule) (a : i.certified.Atom) : Fin 33 :=
  ⟨a.val,by rw [←eq_size i raw]; exact a.isLt⟩

private def perm (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) : Equiv.Perm i.certified.Atom :=
  let f (a : i.certified.Atom) : i.certified.Atom := ⟨rename choice a.val,by
    change rename choice a.val < RingSpatialTransport.size i
    rw [eq_size i raw]
    exact (graph choice (index i raw a)).1⟩
  let inv : Function.Involutive f := fun a => Fin.ext (graph choice (index i raw a)).2.1
  ⟨f,f,inv,inv⟩

private theorem data : ∀ choice : Fin 8, ∀ a : Fin 33,
    molecule.atomZAt (rename choice a.val) = molecule.atomZAt a.val ∧
    molecule.atomMassAt (rename choice a.val) = molecule.atomMassAt a.val := by decide +kernel

private def aut (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) : i.certified.moleculeGraph.Aut := by
  let e := perm choice i raw
  have phys := LocalizedMarkedCertifiedTerminalRefusal.raw_atom_data i.molecule i.certified i.agreement
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a
    rw [(phys _).1,(phys a).1,raw]
    exact (data choice (index i raw a)).1
  · intro a
    rw [(phys _).2,(phys a).2,raw]
    exact (data choice (index i raw a)).2
  · obtain ⟨k,hk⟩ := i.charge
    exact fun a => (hk _).trans (hk a).symm
  · intro a b
    have em : i.certified.moleculeGraph.Adj (e a) (e b) ↔ i.certified.moleculeGraph.Adj a b := by
      rw [raw_adj,raw_adj,raw]
      change 0 < molecule.bondOrder (rename choice a.val) (rename choice b.val) ↔ _
      exact iff_of_eq (congrArg (fun z => 0 < z) ((graph choice (index i raw a)).2.2.2 (index i raw b)))
    by_cases h : i.certified.moleculeGraph.Adj a b
    · rw [i.single _ _ (em.mpr h),i.single _ _ h]
    · have h' := mt em.mp h
      exact (Nat.eq_zero_of_not_pos h').trans (Nat.eq_zero_of_not_pos h).symm

private theorem records (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) :
    RingGeometryAutomorphism.Records (aut choice i raw) := by
  intro a
  change i.molecule.atoms[rename choice a.val]? = _
  rw [raw]
  exact (graph choice (index i raw a)).2.2.1

noncomputable def carrierFor (choice : Fin 8) (i : Input) (raw : i.molecule = molecule) :=
  RingGeometryAutomorphism.carrier (aut choice i raw) (records choice i raw)


private def image (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (q : Site i) : Site i :=
  RingGeometryAutomorphism.site (aut choice i raw) q

private theorem image_history (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (q : Site i) :
    history (image choice raw q) = (history q).map (rename choice) := by
  simp only [history,image,RingGeometryAutomorphism.site,transportOccurrence_node,mapOfficialNode,List.map_map]
  rfl

private theorem fixed (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) : (aut choice i raw).val root = root := by
  apply Fin.ext
  change rename choice root.val = root.val
  rw [zero]
  rfl

private theorem origin_fixed (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) : image choice raw (origin i root) = origin i root := by
  apply site_eq (fixed choice raw root zero)
  rw [image_history]
  change [rename choice root.val] = [root.val]
  rw [zero]
  rfl

theorem swapsFor (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (u v : Fin 4)
    (a : atom fr u = 3) (b : atom fr v = 4) :
    (carrierFor choice i raw).image (cursor fr u) = cursor fr v := by
  have hr := fixed choice raw root zero
  have here : image choice raw (cursor fr u).occurrence = (cursor fr v).occurrence := by
    apply site_eq
    · change (aut choice i raw).val (cursor fr u).occurrence.val.root = _
      exact (congrArg (aut choice i raw).val (fr.direction u).property.1).trans (hr.trans (fr.direction v).property.1.symm)
    · rw [image_history,start,start,a,b,zero]; rfl
  change (⟨image choice raw (cursor fr u).occurrence,some (image choice raw (origin i root))⟩ : Arm i) = _
  rw [here,origin_fixed choice raw root zero]
  rfl

private def tip (n : Nat) : Bool := 9 ≤ n && n < 17
private theorem tip_preserved : ∀ choice : Fin 8, ∀ a : Fin 33, tip (rename choice a.val) = tip a.val := by decide +kernel

/-- The assignment can depend on the entire occurrence, not just the P identifier. -/
def handReader {i : Input} (root : i.certified.Atom) (hand : Site i → RS) : RingNestedActivePair.Reader i :=
  RingSphereQueue.reader root fun q => some <|
    if q.val.node.provenance = .realAtom && (q.val.node.current?.map Fin.val).any tip
      then some (.chiral (hand q),.chiral (hand q).swap) else none

theorem unsignedFor (choice : Fin 8) {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom) (zero : root.val = 0)
    (hand : Site i → RS) : let r := RingSplitLigandTie.markingReader (handReader root hand)
    RingGeometryExchange.Frozen (carrierFor choice i raw) r r := by
  dsimp only
  intro q _
  let t := q.occurrence
  have rootEq : (image choice raw t).val.root = root ↔ t.val.root = root := by
    change (aut choice i raw).val t.val.root = root ↔ _
    nth_rewrite 1 [← fixed choice raw root zero]
    exact (aut choice i raw).val.injective.eq_iff
  have prov : (image choice raw t).val.node.provenance = t.val.node.provenance := rfl
  have tips : ((image choice raw t).val.node.current?.map Fin.val).any tip = (t.val.node.current?.map Fin.val).any tip := by
    change (((t.val.node.current?.map (aut choice i raw).val).map Fin.val).any tip) = _
    cases h : t.val.node.current? with
    | none => rfl
    | some a => exact tip_preserved choice (index i raw a)
  change RingSplitLigandTie.markingReader (handReader root hand) t =
    RingSplitLigandTie.markingReader (handReader root hand) (image choice raw t)
  simp only [RingSplitLigandTie.markingReader,handReader,RingSphereQueue.reader,rootEq,prov,tips]
  split_ifs <;> rfl

noncomputable abbrev carrier := carrierFor 0
theorem swaps {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (u v : Fin 4) (a : atom fr u = 3) (b : atom fr v = 4) :
    (carrier i raw).image (cursor fr u) = cursor fr v := swapsFor 0 raw root zero fr u v a b

theorem unsigned {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom) (zero : root.val = 0)
    (hand : Site i → RS) : let r := RingSplitLigandTie.markingReader (handReader root hand)
    RingGeometryExchange.Frozen (carrier i raw) r r := unsignedFor 0 raw root zero hand

/-- The compact public frozen reader at the carbon origin. -/
def publicReader {i : Input} (root : i.certified.Atom) :=
  RingSphereQueue.reader root (RingSphereQueue.viewOf (RingSparseTwinReport.sparse i root 0))

theorem reader_exact {i : Input} (root : i.certified.Atom)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    publicReader root = RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) (origin i root) := by
  unfold publicReader
  rw [(RingSparseTwinReport.sparse_exact ok root 0).2]
  exact RingGlobalComparison.prior_exact (Or.inr ⟨rfl,rfl⟩)

/-- Verify the location and uppercase status of every tip and absence at all
other sites, ignoring the assigned hands. -/
def unsignedCheck {i : Input} (root : i.certified.Atom) (r : RingNestedActivePair.Reader i) :=
  (LocalizedMarkedCarrierLookup.rootedCarrier i.certified
      (i.certified.certified.input.molecule.atomCount+1) root).all fun q =>
    RingSplitLigandTie.markingReader r q ==
      RingSplitLigandTie.markingReader (handReader root fun _ => .R) q

theorem checked_trial {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (u v : Fin 4)
    (a : atom fr u = 3) (b : atom fr v = 4) (rev : Bool) (ar as' br bs : Nat)
    (status : unsignedCheck root (publicReader root) = true)
    (left : RingEqualPathHandCounts.armCheck i (publicReader root) rev (cursor fr u) ar as' = true)
    (right : RingEqualPathHandCounts.armCheck i (publicReader root) rev (cursor fr v) br bs = true)
    :
    ∃ x y, RingFullPathEligibility.key? i (publicReader root) rev (cursor fr u) = some x ∧
      RingFullPathEligibility.key? i (publicReader root) rev (cursor fr v) = some y ∧
      ∀ m n : RingRetainedChemicalTrace.Word,
        compare (RingFullPathTrialReadings.trialKey x m) (RingFullPathTrialReadings.trialKey y n) =
          (compare (max ar as') (max br bs)).then ((compare ar br).then (compare m n)) := by
  have eqr : RingSplitLigandTie.markingReader (publicReader root) =
      RingSplitLigandTie.markingReader (handReader root fun _ => .R) := by
    funext q
    by_cases rooted : q.val.root = root
    · have atRoot := (i.certified.mem_localizedOccurrences_iff _ _).mp q.property
      have member := (i.certified.mem_localizedOccurrencesAtAtom_iff _ q.val.root q.val).mpr atRoot
      rw [rooted] at member
      exact beq_iff_eq.mp (List.all_eq_true.mp status q
        ((LocalizedMarkedCarrierLookup.mem_rootedCarrier_iff _ _ _ _).mpr member))
    · simp [RingSplitLigandTie.markingReader,publicReader,handReader,RingSphereQueue.reader,rooted]
  have frozen := unsigned raw root zero (fun _ => .R)
  dsimp only at frozen
  rw [← eqr] at frozen
  have dest := swaps raw root zero fr u v a b
  have dom : (carrier i raw).domain (cursor fr u) := by
    intro p hp
    obtain rfl := Option.some.inj hp
    exact (fr.direction u).property.1.symm
  have ready : RingGroupedStereo.Ready (origin i root) (publicReader root) := by
    rw [reader_exact root ok]
    exact RingChemicalGraphProof.ready ok _
  have result := RingEqualPathHandCounts.trial ready (carrier i raw) frozen _ dom
    (RingGroupedCentre.valid fr u) (dest.symm ▸ RingGroupedCentre.valid fr v)
    (fr.direction u).property.1 (dest.symm ▸ (fr.direction v).property.1) rev
    (RingEqualPathHandCounts.armCheck_sound left) (dest.symm ▸ RingEqualPathHandCounts.armCheck_sound right)
  rwa [dest] at result

/-- Each bit denotes an R tip in molecular atom order 9 through 16. -/
def maskHand (mask : Fin 256) (n : Nat) : RS :=
  if tip n && mask.val.testBit (n-9) then .R else .S

private def atSite {i : Input} (mask : Fin 256) (q : Site i) : RS :=
  maskHand mask ((q.val.node.current?.map Fin.val).getD 0)

def signedCheck {i : Input} (root : i.certified.Atom) (r : RingNestedActivePair.Reader i)
    (mask : Fin 256) : Bool :=
  (LocalizedMarkedCarrierLookup.rootedCarrier i.certified
      (i.certified.certified.input.molecule.atomCount+1) root).all fun q =>
    r q == handReader root (atSite mask) q

private def preservesMask (mask : Fin 256) (choice : Fin 8) : Bool :=
  (List.finRange 33).all fun a => maskHand mask (rename choice a.val) == maskHand mask a.val

def matching? (mask : Fin 256) : Option (Fin 8) := (List.finRange 8).find? (preservesMask mask)

/-- Sort the two R counts beneath the two B parents in one arm. -/
def partition (mask : Fin 256) (start : Nat) : List Nat :=
  let count (k : Nat) := (mask.val.testBit k).toNat + (mask.val.testBit (k+1)).toNat
  let a := count start
  let b := count (start+2)
  [min a b,max a b]

theorem matching_iff (mask : Fin 256) :
    (matching? mask).isSome = true ↔ partition mask 0 = partition mask 4 := by
  revert mask
  decide +kernel

/-- One rooted incidence check establishes that the proposed eight hands reproduce
the public reader at every site, including absences. -/
theorem checked_exchange {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) (fr : RingNestedActivePair.Frame i (origin i root)) (u v : Fin 4)
    (a : atom fr u = 3) (b : atom fr v = 4) (mask : Fin 256) (choice : Fin 8)
    (status : signedCheck root (publicReader root) mask = true) (hit : matching? mask = some choice) :
    Nonempty (RingObservedTreeMatch.Unmarked fr (publicReader root) u v) := by
  have same : publicReader root = handReader root (atSite mask) := by
    funext q
    by_cases rooted : q.val.root = root
    · have atRoot := (i.certified.mem_localizedOccurrences_iff _ _).mp q.property
      have member := (i.certified.mem_localizedOccurrencesAtAtom_iff _ q.val.root q.val).mpr atRoot
      rw [rooted] at member
      exact beq_iff_eq.mp (List.all_eq_true.mp status q
        ((LocalizedMarkedCarrierLookup.mem_rootedCarrier_iff _ _ _ _).mpr member))
    · simp [publicReader,handReader,RingSphereQueue.reader,rooted]
  have good : preservesMask mask choice = true := List.find?_some hit
  have invariant (j : i.certified.Atom) : maskHand mask (rename choice j.val) = maskHand mask j.val :=
    beq_iff_eq.mp (List.all_eq_true.mp good (index i raw j) (List.mem_finRange _))
  refine ⟨⟨carrierFor choice i raw,?_,swapsFor choice raw root zero fr u v a b,?_⟩⟩
  · intro p hp
    obtain rfl := Option.some.inj hp
    exact (fr.direction u).property.1.symm
  · rw [same]
    intro q _
    let t := q.occurrence
    have rootEq : (image choice raw t).val.root = root ↔ t.val.root = root := by
      change (aut choice i raw).val t.val.root = root ↔ _
      nth_rewrite 1 [← fixed choice raw root zero]
      exact (aut choice i raw).val.injective.eq_iff
    have prov : (image choice raw t).val.node.provenance = t.val.node.provenance := rfl
    have tips : ((image choice raw t).val.node.current?.map Fin.val).any tip = (t.val.node.current?.map Fin.val).any tip := by
      change (((t.val.node.current?.map (aut choice i raw).val).map Fin.val).any tip) = _
      cases h : t.val.node.current? with
      | none => rfl
      | some j => exact tip_preserved choice (index i raw j)
    have hands : atSite mask (image choice raw t) = atSite mask t := by
      change maskHand mask ((((t.val.node.current?.map (aut choice i raw).val).map Fin.val)).getD 0) = _
      unfold atSite
      cases h : t.val.node.current? with
      | none => rfl
      | some j => exact invariant j
    change handReader root (atSite mask) t = handReader root (atSite mask) (image choice raw t)
    simp only [handReader,RingSphereQueue.reader,rootEq,prov,tips,hands]

end TetraStereo.Examples.ResidualPhosphorusCarrier
assert_kernel_only TetraStereo.Examples.ResidualPhosphorusCarrier.swaps
assert_kernel_only TetraStereo.Examples.ResidualPhosphorusCarrier.unsigned
assert_kernel_only TetraStereo.Examples.ResidualPhosphorusCarrier.checked_trial
assert_kernel_only TetraStereo.Examples.ResidualPhosphorusCarrier.checked_exchange
assert_kernel_only TetraStereo.Examples.ResidualPhosphorusCarrier.matching_iff
