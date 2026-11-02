import TetraStereo.OneCenter.LocalizedCyclicCumulenePerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact molecule-level perception of ordinary monocyclic double bonds

P-93.5.1.4.1 is a rule for monocyclic compounds.  A local occurrence-tree ring closure is not
enough to establish that applicability: the same local event occurs in spiro, fused, bridged, and
other polycyclic systems.  This module therefore works on the complete positive-bond connected
component and requires exactly one independently defined simple cycle.

The carrier is deliberately representation-independent and complete for every finite localized
semantic graph.  It is noncomputable because it uses exhaustive finite subset search plus classical
reachability; no size cap or heuristic is introduced.  A later optimized executable refinement may
replace the search without changing the specification proved here.
-/

namespace CertifiedLocalizedCIPInput

/-- The positive-bond component containing `representative`. -/
noncomputable def localizedCovalentComponentAtoms
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    Finset input.Atom := by
  classical
  exact Finset.univ.filter fun atom =>
    input.moleculeGraph.underlyingSimpleGraph.Reachable representative atom

@[simp] theorem mem_localizedCovalentComponentAtoms_iff
    (input : CertifiedLocalizedCIPInput) (representative atom : input.Atom) :
    atom ∈ input.localizedCovalentComponentAtoms representative ↔
      input.moleculeGraph.underlyingSimpleGraph.Reachable representative atom := by
  classical
  simp [localizedCovalentComponentAtoms]

@[simp] theorem representative_mem_localizedCovalentComponentAtoms
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    representative ∈ input.localizedCovalentComponentAtoms representative := by
  rw [input.mem_localizedCovalentComponentAtoms_iff]

/-- Two representatives joined by positive bonds determine the same complete covalent
component. -/
theorem localizedCovalentComponentAtoms_eq_of_reachable
    (input : CertifiedLocalizedCIPInput) (first second : input.Atom)
    (connected : input.moleculeGraph.underlyingSimpleGraph.Reachable first second) :
    input.localizedCovalentComponentAtoms first =
      input.localizedCovalentComponentAtoms second := by
  apply Finset.ext
  intro atom
  rw [input.mem_localizedCovalentComponentAtoms_iff,
    input.mem_localizedCovalentComponentAtoms_iff]
  constructor
  · intro firstToAtom
    exact connected.symm.trans firstToAtom
  · intro secondToAtom
    exact connected.trans secondToAtom

/-- The underlying molecular graph restricted to edges whose two endpoints lie in `vertices`.
Outside atoms are retained as isolated vertices solely to avoid changing the ambient finite type. -/
def localizedInducedCycleGraph
    (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom) :
    SimpleGraph input.Atom where
  Adj left right := left ∈ vertices ∧ right ∈ vertices ∧
    input.moleculeGraph.Adj left right
  symm := by
    intro left right adjacent
    exact ⟨adjacent.2.1, adjacent.1,
      (input.moleculeGraph.adj_symm).mp adjacent.2.2⟩
  loopless := by
    constructor
    intro atom adjacent
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent

@[simp] theorem localizedInducedCycleGraph_adj
    (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom)
    (left right : input.Atom) :
    (input.localizedInducedCycleGraph vertices).Adj left right ↔
      left ∈ vertices ∧ right ∈ vertices ∧
        input.moleculeGraph.Adj left right :=
  Iff.rfl

/-- Positive-bond neighbours of `atom` retained inside a candidate cycle vertex set. -/
def localizedCycleNeighbors
    (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom)
    (atom : input.Atom) : Finset input.Atom :=
  (input.moleculeGraph.neighborFinset atom).filter fun neighbor => neighbor ∈ vertices

@[simp] theorem mem_localizedCycleNeighbors_iff
    (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom)
    (atom neighbor : input.Atom) :
    neighbor ∈ input.localizedCycleNeighbors vertices atom ↔
      neighbor ∈ vertices ∧ input.moleculeGraph.Adj atom neighbor := by
  simp [localizedCycleNeighbors, and_comm]

/-- Independent finite-graph meaning of one simple cycle vertex set:

* at least three vertices;
* every retained vertex has exactly two retained positive-bond neighbours; and
* every pair of retained vertices is connected without leaving the set.

The last condition prevents a disjoint union of cycles from being accepted as one ring. -/
def DeclarativeLocalizedSimpleCycleVertexSet
    (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom) : Prop :=
  3 ≤ vertices.card ∧
    (∀ atom, atom ∈ vertices →
      (input.localizedCycleNeighbors vertices atom).card = 2) ∧
    ∀ left, left ∈ vertices → ∀ right, right ∈ vertices →
      (input.localizedInducedCycleGraph vertices).Reachable left right

/-- All simple cycles contained in the positive-bond component of `representative`.  Exhaustive
powerset search makes this a complete finite specification, not a smallest-ring heuristic. -/
noncomputable def localizedSimpleCycleVertexSetsInComponent
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom) :
    Finset (Finset input.Atom) := by
  classical
  exact (Finset.univ : Finset input.Atom).powerset.filter fun vertices =>
    input.DeclarativeLocalizedSimpleCycleVertexSet vertices ∧
      vertices ⊆ input.localizedCovalentComponentAtoms representative

@[simp] theorem mem_localizedSimpleCycleVertexSetsInComponent_iff
    (input : CertifiedLocalizedCIPInput) (representative : input.Atom)
    (vertices : Finset input.Atom) :
    vertices ∈ input.localizedSimpleCycleVertexSetsInComponent representative ↔
      input.DeclarativeLocalizedSimpleCycleVertexSet vertices ∧
        vertices ⊆ input.localizedCovalentComponentAtoms representative := by
  classical
  simp [localizedSimpleCycleVertexSetsInComponent]

/-- Number of physical order-two edges internal to a finite vertex set.  Strict endpoint order
counts each undirected bond exactly once. -/
def localizedDoubleBondCountIn
    (input : CertifiedLocalizedCIPInput) (vertices : Finset input.Atom) : Nat :=
  ((Finset.univ : Finset input.Atom) ×ˢ (Finset.univ : Finset input.Atom)).filter
    (fun edge => edge.1 < edge.2 ∧ edge.1 ∈ vertices ∧ edge.2 ∈ vertices ∧
      input.moleculeGraph.bond edge.1 edge.2 = 2) |>.card

/-- Public carrier for the unique ordinary monocycle containing an oriented double bond. -/
structure LocalizedMonocyclicDoubleBond
    (input : CertifiedLocalizedCIPInput) where
  ring : Finset input.Atom
  deriving DecidableEq

/-- Independent meaning of an ordinary monocyclic double-bond carrier.  Uniqueness is imposed on
all simple cycles in the complete connected component, excluding spiro/fused/bridged components.
The strict double-bond-count inequality separates a fully all-double cyclic cumulene. -/
def DeclarativeLocalizedMonocyclicDoubleBond
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (carrier : input.LocalizedMonocyclicDoubleBond) : Prop :=
  input.moleculeGraph.bond left right = 2 ∧
    left ∈ carrier.ring ∧ right ∈ carrier.ring ∧
    input.DeclarativeLocalizedSimpleCycleVertexSet carrier.ring ∧
    carrier.ring ⊆ input.localizedCovalentComponentAtoms left ∧
    (∀ other,
      input.DeclarativeLocalizedSimpleCycleVertexSet other →
      other ⊆ input.localizedCovalentComponentAtoms left →
      other = carrier.ring) ∧
    input.localizedDoubleBondCountIn carrier.ring < carrier.ring.card

/-- Exhaustively perceive the ordinary monocycle containing `left=right`.  Successful output
requires exactly one simple cycle in the complete component and refuses an all-double cycle. -/
noncomputable def localizedMonocyclicDoubleBondAt?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    Option input.LocalizedMonocyclicDoubleBond := by
  classical
  let cycles := input.localizedSimpleCycleVertexSetsInComponent left
  exact match cycles.toList with
  | [ring] =>
      if input.moleculeGraph.bond left right = 2 ∧
          left ∈ ring ∧ right ∈ ring ∧
          input.localizedDoubleBondCountIn ring < ring.card then
        some { ring := ring }
      else none
  | _ => none

/-- Successful monocycle perception is exactly the independent unique-cycle predicate. -/
theorem localizedMonocyclicDoubleBondAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (carrier : input.LocalizedMonocyclicDoubleBond) :
    input.localizedMonocyclicDoubleBondAt? left right = some carrier ↔
      input.DeclarativeLocalizedMonocyclicDoubleBond left right carrier := by
  classical
  let cycles := input.localizedSimpleCycleVertexSetsInComponent left
  constructor
  · intro computed
    unfold localizedMonocyclicDoubleBondAt? at computed
    change (match cycles.toList with
      | [ring] =>
          if input.moleculeGraph.bond left right = 2 ∧
              left ∈ ring ∧ right ∈ ring ∧
              input.localizedDoubleBondCountIn ring < ring.card then
            some { ring := ring }
          else none
      | _ => none) = some carrier at computed
    cases cyclesList : cycles.toList with
    | nil => simp [cyclesList] at computed
    | cons ring tail =>
        cases tail with
        | cons second rest => simp [cyclesList] at computed
        | nil =>
            simp only [cyclesList] at computed
            split at computed
            · rename_i accepted
              have carrierIdentity : ({ ring := ring } :
                  input.LocalizedMonocyclicDoubleBond) = carrier :=
                Option.some.inj computed
              subst carrier
              have ringPresent : ring ∈ cycles := by
                have : ring ∈ cycles.toList := by simp [cyclesList]
                simpa using this
              have ringMeaning :=
                (input.mem_localizedSimpleCycleVertexSetsInComponent_iff
                  left ring).mp ringPresent
              refine ⟨accepted.1, accepted.2.1, accepted.2.2.1,
                ringMeaning.1, ringMeaning.2, ?_, accepted.2.2.2⟩
              intro other otherCycle otherSubset
              have otherPresent : other ∈ cycles :=
                (input.mem_localizedSimpleCycleVertexSetsInComponent_iff
                  left other).mpr ⟨otherCycle, otherSubset⟩
              have otherList : other ∈ cycles.toList := by simpa using otherPresent
              simpa [cyclesList] using otherList
            · simp at computed
  · intro derived
    have cyclesIdentity : cycles = {carrier.ring} := by
      apply Finset.ext
      intro other
      constructor
      · intro otherPresent
        have otherMeaning :=
          (input.mem_localizedSimpleCycleVertexSetsInComponent_iff
            left other).mp otherPresent
        have equal := derived.2.2.2.2.2.1 other otherMeaning.1 otherMeaning.2
        simp [equal]
      · intro otherSingleton
        have equal : other = carrier.ring := by simpa using otherSingleton
        subst other
        exact (input.mem_localizedSimpleCycleVertexSetsInComponent_iff
          left carrier.ring).mpr ⟨derived.2.2.2.1, derived.2.2.2.2.1⟩
    unfold localizedMonocyclicDoubleBondAt?
    change (match cycles.toList with
      | [ring] =>
          if input.moleculeGraph.bond left right = 2 ∧
              left ∈ ring ∧ right ∈ ring ∧
              input.localizedDoubleBondCountIn ring < ring.card then
            some { ring := ring }
          else none
      | _ => none) = some carrier
    rw [cyclesIdentity]
    simp [derived.1, derived.2.1, derived.2.2.1,
      derived.2.2.2.2.2.2]

/-- Perception returns `none` exactly when no independently valid ordinary monocyclic carrier
contains the oriented double bond. -/
theorem localizedMonocyclicDoubleBondAt?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedMonocyclicDoubleBondAt? left right = none ↔
      ∀ carrier, ¬input.DeclarativeLocalizedMonocyclicDoubleBond
        left right carrier := by
  constructor
  · intro computed carrier derived
    have shouldCompute :=
      (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
        left right carrier).mpr derived
    rw [computed] at shouldCompute
    simp at shouldCompute
  · intro absent
    cases computed : input.localizedMonocyclicDoubleBondAt? left right with
    | none => rfl
    | some carrier =>
        have derived :=
          (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
            left right carrier).mp computed
        exact (absent carrier derived).elim

/-- Perception cannot classify a fully all-double ring as an ordinary monocyclic double-bond
system. -/
theorem DeclarativeLocalizedMonocyclicDoubleBond.not_fully_double
    (input : CertifiedLocalizedCIPInput) {left right : input.Atom}
    {carrier : input.LocalizedMonocyclicDoubleBond}
    (derived : input.DeclarativeLocalizedMonocyclicDoubleBond left right carrier) :
    input.localizedDoubleBondCountIn carrier.ring ≠ carrier.ring.card :=
  ne_of_lt derived.2.2.2.2.2.2

/-- The independent monocyclic-double-bond meaning is insensitive to the arbitrary orientation
of the physical double bond. -/
theorem DeclarativeLocalizedMonocyclicDoubleBond.swap
    (input : CertifiedLocalizedCIPInput) {left right : input.Atom}
    {carrier : input.LocalizedMonocyclicDoubleBond}
    (derived : input.DeclarativeLocalizedMonocyclicDoubleBond left right carrier) :
    input.DeclarativeLocalizedMonocyclicDoubleBond right left carrier := by
  have adjacent : input.moleculeGraph.underlyingSimpleGraph.Adj left right := by
    change 0 < input.moleculeGraph.bond left right
    simp [derived.1]
  have componentsEqual := input.localizedCovalentComponentAtoms_eq_of_reachable
    left right adjacent.reachable
  refine ⟨?_, derived.2.2.1, derived.2.1, derived.2.2.2.1, ?_, ?_,
    derived.2.2.2.2.2.2⟩
  · simpa [input.moleculeGraph.bond_symm left right] using derived.1
  · simpa [componentsEqual] using derived.2.2.2.2.1
  · intro other otherCycle otherSubset
    apply derived.2.2.2.2.2.1 other otherCycle
    simpa [componentsEqual] using otherSubset

/-- Exact monocycle perception returns the same carrier after reversing a physical double
bond. -/
theorem localizedMonocyclicDoubleBondAt?_swap
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedMonocyclicDoubleBondAt? left right =
      input.localizedMonocyclicDoubleBondAt? right left := by
  cases leftComputed : input.localizedMonocyclicDoubleBondAt? left right with
  | none =>
      cases rightComputed : input.localizedMonocyclicDoubleBondAt? right left with
      | none => simp
      | some carrier =>
          have rightDerived :=
            (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
              right left carrier).mp rightComputed
          have leftShouldCompute :=
            (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
              left right carrier).mpr rightDerived.swap
          simp [leftComputed] at leftShouldCompute
  | some carrier =>
      have leftDerived :=
        (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
          left right carrier).mp leftComputed
      have rightShouldCompute :=
        (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
          right left carrier).mpr leftDerived.swap
      exact rightShouldCompute.symm

/-- P-93.5.1.4.1 policy selected for one exactly perceived ordinary monocyclic double bond. -/
structure LocalizedMonocyclicDoubleBondPolicyResult
    (input : CertifiedLocalizedCIPInput) where
  carrier : input.LocalizedMonocyclicDoubleBond
  doubleBondCount : Nat
  policy : BlueBookP93.Cyclic.DoubleBondDescriptorPolicy
  deriving DecidableEq

/-- Apply the independent P-91/P-93 ring-size policy only after exact monocycle perception. -/
noncomputable def localizedMonocyclicDoubleBondPolicyAt?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    Option input.LocalizedMonocyclicDoubleBondPolicyResult := do
  let carrier ← input.localizedMonocyclicDoubleBondAt? left right
  let doubleBondCount := input.localizedDoubleBondCountIn carrier.ring
  let policy ← BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
    carrier.ring.card doubleBondCount
  some { carrier, doubleBondCount, policy }

/-- Ring-size/count policy selection is likewise independent of the stored endpoint order. -/
theorem localizedMonocyclicDoubleBondPolicyAt?_swap
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedMonocyclicDoubleBondPolicyAt? left right =
      input.localizedMonocyclicDoubleBondPolicyAt? right left := by
  unfold localizedMonocyclicDoubleBondPolicyAt?
  rw [input.localizedMonocyclicDoubleBondAt?_swap left right]

/-- Independent exact meaning of a returned cyclic-double-bond policy. -/
def DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedMonocyclicDoubleBondPolicyResult) : Prop :=
  input.DeclarativeLocalizedMonocyclicDoubleBond left right result.carrier ∧
    result.doubleBondCount = input.localizedDoubleBondCountIn result.carrier.ring ∧
    BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
      result.carrier.ring.card result.doubleBondCount = some result.policy

/-- Production policy selection is sound and complete with respect to exact monocycle perception
and the independent P-91/P-93 ring-size policy. -/
theorem localizedMonocyclicDoubleBondPolicyAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedMonocyclicDoubleBondPolicyResult) :
    input.localizedMonocyclicDoubleBondPolicyAt? left right = some result ↔
      input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult left right result := by
  unfold localizedMonocyclicDoubleBondPolicyAt?
  cases carrierComputed : input.localizedMonocyclicDoubleBondAt? left right with
  | none =>
      constructor
      · simp
      · intro derived
        have shouldCompute :=
          (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
            left right result.carrier).mpr derived.1
        simp [carrierComputed] at shouldCompute
  | some carrier =>
      cases policyComputed : BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
          carrier.ring.card (input.localizedDoubleBondCountIn carrier.ring) with
      | none =>
          constructor
          · simp [policyComputed]
          · intro derived
            have shouldCompute :=
              (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
                left right result.carrier).mpr derived.1
            have carrierIdentity : carrier = result.carrier :=
              Option.some.inj (carrierComputed.symm.trans shouldCompute)
            cases carrierIdentity
            have impossible := derived.2.2
            rw [derived.2.1, policyComputed] at impossible
            simp at impossible
      | some policy =>
          constructor
          · intro computed
            simp [policyComputed] at computed
            subst result
            exact ⟨
              (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
                left right carrier).mp carrierComputed,
              rfl, policyComputed⟩
          · intro derived
            have shouldCompute :=
              (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
                left right result.carrier).mpr derived.1
            have carrierIdentity : carrier = result.carrier :=
              Option.some.inj (carrierComputed.symm.trans shouldCompute)
            cases carrierIdentity
            cases result with
            | mk resultCarrier resultCount resultPolicy =>
                have countIdentity : resultCount =
                    input.localizedDoubleBondCountIn resultCarrier.ring := derived.2.1
                subst resultCount
                have policyIdentity : policy = resultPolicy := by
                  have derivedPolicy :
                      BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
                        resultCarrier.ring.card
                          (input.localizedDoubleBondCountIn resultCarrier.ring) =
                        some resultPolicy := derived.2.2
                  rw [policyComputed] at derivedPolicy
                  exact Option.some.inj derivedPolicy
                subst resultPolicy
                simp [policyComputed]

/-- A returned mandatory-`E/Z` policy has exactly the independently transcribed P-91/P-93 ring
size/count applicability. -/
theorem DeclarativeLocalizedMonocyclicDoubleBondPolicyResult.requireEZ_authority
    (input : CertifiedLocalizedCIPInput) {left right : input.Atom}
    {result : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (derived : input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
      left right result)
    (required : result.policy = .requireEZ) :
    (result.carrier.ring.card = 8 ∧ result.doubleBondCount = 1) ∨
      9 ≤ result.carrier.ring.card := by
  apply (BlueBookP93.Cyclic.monocyclicDoubleBondPolicy_eq_requireEZ_iff
    result.carrier.ring.card result.doubleBondCount).mp
  simpa [required] using derived.2.2

/-- A returned permanent-omission policy has exactly the independently transcribed small-ring or
special eight-membered-polyene applicability. -/
theorem DeclarativeLocalizedMonocyclicDoubleBondPolicyResult.permanentlyOmit_authority
    (input : CertifiedLocalizedCIPInput) {left right : input.Atom}
    {result : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (derived : input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
      left right result)
    (omitted : result.policy = .permanentlyOmit) :
    (3 ≤ result.carrier.ring.card ∧ result.carrier.ring.card ≤ 7) ∨
      (result.carrier.ring.card = 8 ∧ 2 ≤ result.doubleBondCount ∧
        result.doubleBondCount ≤ 4) := by
  apply (BlueBookP93.Cyclic.monocyclicDoubleBondPolicy_eq_permanentlyOmit_iff
    result.carrier.ring.card result.doubleBondCount).mp
  simpa [omitted] using derived.2.2

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
