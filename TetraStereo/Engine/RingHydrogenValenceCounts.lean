import TetraStereo.Engine.RingProducedHydrogenGraphs
import TetraStereo.Engine.RingHydrogenNeighbors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace TetraStereo.OneCenter.OrdinaryHydrogenSpellings.Production
open TetraStereo.Engine.RingHydrogenCompletion
open scoped BigOperators

variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

def heavyBondSum (coreBond : Fin k → Fin k → Nat) (c : Fin k) : Nat := ∑ d, coreBond c d

private theorem coreFiber_card (a : Completion coreAtom coreBond) (d : Fin k) :
    Fintype.card (a.Fiber (.inl d)) = 1 := by
  classical
  apply Fintype.card_eq_one_iff.mpr
  exact ⟨⟨a.core d,a.core_tag d⟩, fun v => Subtype.ext (a.core_only v.val d v.property)⟩

/-- The physical weighted graph valence splits into the common heavy-core contribution
and the actual existing ordinary-H fiber cardinality. -/
theorem bondSum_decomposition (a : Completion coreAtom coreBond) (c : Fin k) :
    (∑ v : a.Vertex, a.molecule.bondOrder (a.core c).val v.val) =
      heavyBondSum coreBond c + a.hydrogenCount c := by
  classical
  calc
    _ = ∑ t : Fin k ⊕ Fin k, ∑ v : a.Fiber t,
        a.molecule.bondOrder (a.core c).val v.val.val :=
      (Fintype.sum_fiberwise a.tag (fun v => a.molecule.bondOrder (a.core c).val v.val)).symm
    _ = ∑ t : Fin k ⊕ Fin k, ∑ _v : a.Fiber t, bondTable coreBond (.inl c) t := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro v _
      rw [a.bonds,a.core_tag,v.property]
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [bondTable,coreFiber_card,Completion.hydrogenCount,heavyBondSum]

private theorem getCompat {α : Type} (xs : List α) (n : Nat) : listGet? xs n = xs[n]? := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih => cases n with
    | zero => rfl
    | succ n => exact ih n

/-- The native policy fills an unbracketed nonaromatic carbon to valence four.
This exposes its actual raw-record incident sum, rather than replacing it by a graph sum. -/
theorem missing_unbracketed_carbon (m : RawMolecule) (j : Nat) (atom : AtomSpec)
    (lookup : m.atoms[j]? = some atom) (carbon : atom.element = .C)
    (aliphatic : atom.aromatic = false) (unbracketed : atom.explicitHydrogens? = none)
    (allowed : m.incidentBondOrderSum j ≤ 4) :
    missing m j = 4 - m.incidentBondOrderSum j := by
  have closedSum : (closeHydrogenVertices m).incidentBondOrderSum j = m.incidentBondOrderSum j := rfl
  simp [missing,RawMolecule.hydrogenCountAt,RawMolecule.atomAt?,getCompat,closeHydrogenVertices,
    closeAtom,lookup,carbon,unbracketed,aliphatic,RawMolecule.defaultValences,
    RawMolecule.elementDefaultValences, List.getElem?_map, Option.map_some,
    Bool.false_eq_true, List.find?_cons, List.find?_nil]
  change (match (match decide (m.incidentBondOrderSum j ≤ 4) with
      | true => some 4 | false => none) with
    | some valence => valence - m.incidentBondOrderSum j
    | none => 0) = _
  simp [allowed]

private theorem foldMax (bs : List RawBond) (p : RawBond → Bool) (acc : Nat) :
    bs.foldl (fun x b => if p b then max x b.kind.order else x) acc =
      max acc (bs.foldr (fun b x => max (if p b then b.kind.order else 0) x) 0) := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons,ih,List.foldr_cons]
    cases p b <;> simp [Nat.max_assoc]

private theorem maxPair (bs : List RawBond) (p q : RawBond → Bool) :
    max (bs.foldr (fun b x => max (if p b then b.kind.order else 0) x) 0)
      (bs.foldr (fun b x => max (if q b then b.kind.order else 0) x) 0) =
    bs.foldr (fun b x => max (if p b || q b then b.kind.order else 0) x) 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldr_cons]
    cases p b <;> cases q b <;> simp_all [Nat.max_assoc,Nat.max_left_comm,Nat.max_comm]

private theorem recordCount_le_one (m : RawMolecule) (unique : m.BondRecordsUnique) (u v : Nat) :
    m.bonds.countP (fun b => b.connects u v) ≤ 1 := by
  let key := (min u v,max u v)
  have keys (b : RawBond) (hit : b.connects u v = true) : b.edgeKey = key := by
    simp only [RawBond.connects,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at hit
    rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [key,RawBond.edgeKey,Nat.min_comm,Nat.max_comm]
  have bound : m.bonds.countP (fun b => b.connects u v) ≤ (m.bonds.map RawBond.edgeKey).count key := by
    induction m.bonds with
    | nil => simp
    | cons b bs ih =>
      simp only [List.countP_cons,List.map_cons,List.count_cons]
      cases hit : b.connects u v with
      | false => simp; omega
      | true => simp [keys b hit]; omega
  exact bound.trans ((List.nodup_iff_count_le_one.mp unique) key)

private theorem maxFold_sum (bs : List RawBond) (p : RawBond → Bool)
    (unique : bs.countP p ≤ 1) :
    bs.foldr (fun b x => max (if p b then b.kind.order else 0) x) 0 =
      (bs.map (fun b => if p b then b.kind.order else 0)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases hit : p b with
    | false =>
      have tail : bs.countP p ≤ 1 := by simpa [List.countP_cons,hit] using unique
      simpa [hit] using ih tail
    | true =>
      have zero : bs.countP p = 0 := by simpa [List.countP_cons,hit] using unique
      have zeroMap : bs.map (fun b => if p b then b.kind.order else 0) = bs.map (fun _ => 0) := by
        apply List.map_congr_left
        intro t mem
        have no := List.countP_eq_zero.mp zero t mem
        simp [no]
      have tail := ih (by omega)
      simp [hit,tail,zeroMap]

/-- Under unordered-record uniqueness, graph bond order equals the native per-pair record sum. -/
theorem admitted_pair_record_sum (m : RawMolecule) (unique : m.BondRecordsUnique)
    (u v : Nat) (different : u ≠ v) :
    m.bondOrder u v = (m.bonds.map (fun b => if b.connects u v then b.kind.order else 0)).sum := by
  unfold RawMolecule.bondOrder RawMolecule.directedBondOrder
  rw [if_neg different,foldMax,foldMax]
  simp only [Nat.zero_max]
  have merged := maxPair m.bonds (fun b => b.directedConnects u v) (fun b => b.directedConnects v u)
  have predicate : (fun b : RawBond => b.directedConnects u v || b.directedConnects v u) =
      (fun b => b.connects u v) := by
    funext b
    simp [RawBond.directedConnects,RawBond.connects]
  rw [merged]
  have pred (b : RawBond) : (b.directedConnects u v || b.directedConnects v u) = b.connects u v := congrFun predicate b
  simp_rw [pred]
  exact maxFold_sum _ _ (recordCount_le_one m unique u v)

private theorem pair_record_sum (m : RawMolecule) (admitted : m.Admissible) (u v : Nat) :
    m.bondOrder u v = (m.bonds.map (fun b => if b.connects u v then b.kind.order else 0)).sum := by
  by_cases different : u ≠ v
  · exact admitted_pair_record_sum m admitted.2 u v different
  · have same : u = v := by omega
    subst v
    rw [m.bondOrder_self]
    have zeros : m.bonds.map (fun b => if b.connects u u then b.kind.order else 0) = m.bonds.map (fun _ => 0) := by
      apply List.map_congr_left
      intro b mem
      have noLoop := (admitted.1 b mem).2.2
      simp only [RawBond.connects,Bool.or_self,Bool.and_eq_true,beq_iff_eq]
      split
      · rename_i hit
        exact False.elim (noLoop (hit.1.trans hit.2.symm))
      · rfl
    rw [zeros]
    simp

private theorem one_record_sum (m : RawMolecule) (b : RawBond) (bounded : m.BondEndpointsOK b)
    (u : Fin m.atomCount) :
    (∑ v : Fin m.atomCount, if b.connects u.val v.val then b.kind.order else 0) =
      RawMolecule.incidentContributionAt u.val b := by
  have s : ∀ v : Fin m.atomCount, b.source = v.val ↔ (⟨b.source,bounded.1⟩ : Fin m.atomCount) = v := by
    intro v
    constructor
    · intro eq; apply Fin.ext; exact eq
    · intro eq; exact congrArg Fin.val eq
  have t : ∀ v : Fin m.atomCount, b.target = v.val ↔ (⟨b.target,bounded.2.1⟩ : Fin m.atomCount) = v := by
    intro v
    constructor
    · intro eq; apply Fin.ext; exact eq
    · intro eq; exact congrArg Fin.val eq
  by_cases source : b.source = u.val
  · have notTarget : b.target ≠ u.val := fun eq => bounded.2.2 (source.trans eq.symm)
    simp only [RawBond.connects,source,beq_self_eq_true,Bool.true_and,
      beq_eq_false_iff_ne.mpr notTarget,Bool.and_false,Bool.or_false,
      RawMolecule.incidentContributionAt,if_true]
    simp only [beq_iff_eq,t]
    simp
  · by_cases target : b.target = u.val
    · simp only [RawBond.connects,target,beq_self_eq_true,Bool.and_true,
        beq_eq_false_iff_ne.mpr source,Bool.false_and,Bool.false_or,
        RawMolecule.incidentContributionAt,Bool.or_true,if_true]
      simp only [beq_iff_eq,s]
      simp
    · simp [RawBond.connects,RawMolecule.incidentContributionAt,source,target]

/-- Standard raw admission suffices: uniqueness makes max-based bondOrder agree with
record addition; endpoint validity makes the vertex sum count every incident record once. -/
theorem native_incident_eq_graph_sum (m : RawMolecule) (admitted : m.Admissible)
    (u : Fin m.atomCount) :
    m.incidentBondOrderSum u.val = ∑ v : Fin m.atomCount, m.bondOrder u.val v.val := by
  rw [RawMolecule.incidentBondOrderSum_eq_incidentContributionAt_sum]
  simp_rw [pair_record_sum m admitted]
  have exchange (bs : List RawBond) :
      (∑ v : Fin m.atomCount, (bs.map (fun b => if b.connects u.val v.val then b.kind.order else 0)).sum) =
      (bs.map (fun b => ∑ v : Fin m.atomCount, if b.connects u.val v.val then b.kind.order else 0)).sum := by
    induction bs with
    | nil => simp
    | cons b bs ih => simp [Finset.sum_add_distrib,ih]
  rw [exchange]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b mem
  exact (one_record_sum m b (admitted.1 b mem) u).symm

/-- Native carbon H totals depend only on the heavy-core valence once the local raw-record
incident sum agrees with the weighted graph sum. The local relation is explicit here. -/
theorem unbracketed_carbon_total_of_native_sum (a : Completion coreAtom coreBond) (c : Fin k)
    (atom : AtomSpec) (lookup : a.molecule.atoms[(a.core c).val]? = some atom)
    (carbon : atom.element = .C) (aliphatic : atom.aromatic = false)
    (unbracketed : atom.explicitHydrogens? = none)
    (native : a.molecule.incidentBondOrderSum (a.core c).val =
      ∑ v : a.Vertex, a.molecule.bondOrder (a.core c).val v.val)
    (allowed : a.molecule.incidentBondOrderSum (a.core c).val ≤ 4) :
    a.hydrogenCount c + missing a.molecule (a.core c).val = 4-heavyBondSum coreBond c := by
  rw [missing_unbracketed_carbon a.molecule _ atom lookup carbon aliphatic unbracketed allowed]
  have sum := bondSum_decomposition a c
  rw [native] at allowed ⊢
  rw [sum] at allowed ⊢
  omega

/-- The full native parent total, using the executable parent-list count rather than `missing`. -/
theorem unbracketed_carbon_planned_total_of_native_sum (a : Completion coreAtom coreBond) (c : Fin k)
    (atom : AtomSpec) (lookup : a.molecule.atoms[(a.core c).val]? = some atom)
    (carbon : atom.element = .C) (aliphatic : atom.aromatic = false)
    (unbracketed : atom.explicitHydrogens? = none)
    (native : a.molecule.incidentBondOrderSum (a.core c).val =
      ∑ v : a.Vertex, a.molecule.bondOrder (a.core c).val v.val)
    (allowed : a.molecule.incidentBondOrderSum (a.core c).val ≤ 4) :
    a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val = 4-heavyBondSum coreBond c := by
  rw [TetraStereo.Engine.RingPyramidalChoices.addedParents_count _ _ (a.core c).isLt]
  exact unbracketed_carbon_total_of_native_sum a c atom lookup carbon aliphatic unbracketed native allowed

/-- Raw admission discharges the native/graph relation; no additional valence-equality
or per-parent H-total hypothesis is needed for the unbracketed aliphatic carbon case. -/
theorem unbracketed_carbon_planned_total (a : Completion coreAtom coreBond) (c : Fin k)
    (admitted : a.molecule.Admissible)
    (atom : AtomSpec) (lookup : a.molecule.atoms[(a.core c).val]? = some atom)
    (carbon : atom.element = .C) (aliphatic : atom.aromatic = false)
    (unbracketed : atom.explicitHydrogens? = none)
    (allowed : a.molecule.incidentBondOrderSum (a.core c).val ≤ 4) :
    a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val = 4-heavyBondSum coreBond c :=
  unbracketed_carbon_planned_total_of_native_sum a c atom lookup carbon aliphatic unbracketed
    (native_incident_eq_graph_sum a.molecule admitted (a.core c)) allowed

/-- Ordinary neutral unbracketed carbon with native written valence at most four. -/
def OrdinaryCarbonAt (a : Completion coreAtom coreBond) (c : Fin k) : Prop :=
  ∃ atom, a.molecule.atoms[(a.core c).val]? = some atom ∧ atom.element = .C ∧
    atom.aromatic = false ∧ atom.charge = 0 ∧ atom.explicitHydrogens? = none ∧
    a.molecule.incidentBondOrderSum (a.core c).val ≤ 4

theorem ordinary_carbon_totals_agree (a b : Completion coreAtom coreBond)
    (aAdmitted : a.molecule.Admissible) (bAdmitted : b.molecule.Admissible)
    (aCarbon : ∀ c, OrdinaryCarbonAt a c) (bCarbon : ∀ c, OrdinaryCarbonAt b c) (c : Fin k) :
    a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val =
      b.hydrogenCount c + (addedParents b.molecule).count (b.core c).val := by
  obtain ⟨atomA,lookupA,carbonA,aliphaticA,_,unbracketedA,allowedA⟩ := aCarbon c
  obtain ⟨atomB,lookupB,carbonB,aliphaticB,_,unbracketedB,allowedB⟩ := bCarbon c
  rw [unbracketed_carbon_planned_total a c aAdmitted atomA lookupA carbonA aliphaticA unbracketedA allowedA,
    unbracketed_carbon_planned_total b c bAdmitted atomB lookupB carbonB aliphaticB unbracketedB allowedB]

/-- For ordinary unbracketed carbon cores, successful actual preparations construct matching
output graphs without any supplied atom bijection, output certificate, or H-total equality. -/
theorem prepared_ordinary_carbon_bijection (a b : Completion coreAtom coreBond)
    (aCarbon : ∀ c, OrdinaryCarbonAt a c) (bCarbon : ∀ c, OrdinaryCarbonAt b c)
    {xyzA xyzB : SpatialConfiguration} {ra rb : RawMolecule × SpatialConfiguration}
    (acceptedA : prepare? a.molecule xyzA = some ra)
    (acceptedB : prepare? b.molecule xyzB = some rb) :
    ∃ e : Fin ra.1.atomCount ≃ Fin rb.1.atomCount,
      (∀ c, (e ⟨(a.core c).val,lt_of_lt_of_le (a.core c).isLt
        (prepare?_certified acceptedA).atomCount_le⟩).val = (b.core c).val) ∧
      (∀ v, heavyCore (rb.1.atoms.get (e v)) = heavyCore (ra.1.atoms.get v)) ∧
      (∀ v w, rb.1.bondOrder (e v).val (e w).val = ra.1.bondOrder v.val w.val) := by
  apply prepared_spellings_bijection a b acceptedA acceptedB
  exact ordinary_carbon_totals_agree a b (prepare?_certified acceptedA).input_admissible.1
    (prepare?_certified acceptedB).input_admissible.1 aCarbon bCarbon

/-- General native search result: unbracketed nonhydrogen atoms fill to the selected valence. -/
theorem missing_selected_valence (m : RawMolecule) (j : Nat) (atom : AtomSpec) (V : Nat)
    (lookup : m.atoms[j]? = some atom) (nonHydrogen : atom.element ≠ .H)
    (unbracketed : atom.explicitHydrogens? = none)
    (selected : (RawMolecule.defaultValences atom).find?
      (fun v => decide (m.incidentBondOrderSum j ≤ v)) = some V) :
    missing m j = V - m.incidentBondOrderSum j := by
  simp [missing,closeHydrogenVertices,RawMolecule.hydrogenCountAt,RawMolecule.atomAt?,
    getCompat,lookup,closeAtom,nonHydrogen,unbracketed]
  change (match (RawMolecule.defaultValences atom).find?
      (fun v => decide (m.incidentBondOrderSum j ≤ v)) with
    | some valence => valence-m.incidentBondOrderSum j | none => 0) = _
  rw [selected]

/-- Any common selected native valence gives the same per-parent H total. -/
theorem selected_valence_planned_total (a : Completion coreAtom coreBond) (c : Fin k)
    (admitted : a.molecule.Admissible) (atom : AtomSpec) (V : Nat)
    (lookup : a.molecule.atoms[(a.core c).val]? = some atom)
    (nonHydrogen : atom.element ≠ .H) (unbracketed : atom.explicitHydrogens? = none)
    (selected : (RawMolecule.defaultValences atom).find?
      (fun v => decide (a.molecule.incidentBondOrderSum (a.core c).val ≤ v)) = some V) :
    a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val =
      V-heavyBondSum coreBond c := by
  rw [TetraStereo.Engine.RingPyramidalChoices.addedParents_count _ _ (a.core c).isLt,
    missing_selected_valence a.molecule _ atom V lookup nonHydrogen unbracketed selected]
  have bounded : a.molecule.incidentBondOrderSum (a.core c).val ≤ V := by
    have hit := List.find?_some
      (p := fun v => decide (a.molecule.incidentBondOrderSum (a.core c).val ≤ v)) selected
    exact of_decide_eq_true hit
  have native := native_incident_eq_graph_sum a.molecule admitted (a.core c)
  have split := bondSum_decomposition a c
  rw [native,split] at bounded ⊢
  omega

@[simp] theorem defaultValences_heavyCore (atom : AtomSpec) :
    RawMolecule.defaultValences (heavyCore atom) = RawMolecule.defaultValences atom := rfl

/-- The first value of the common heavy record's native valence list is automatically selected
whenever the actual written valence already fits it. This covers mixed C/N/O/halogen cores. -/
theorem first_valence_planned_total (a : Completion coreAtom coreBond) (c : Fin k)
    (admitted : a.molecule.Admissible) (V : Nat)
    (nonH : (coreAtom c).element ≠ .H)
    (first : (RawMolecule.defaultValences (coreAtom c)).head? = some V)
    (unbracketed : (a.molecule.atoms.get (a.core c)).explicitHydrogens? = none)
    (allowed : a.molecule.incidentBondOrderSum (a.core c).val ≤ V) :
    a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val =
      V-heavyBondSum coreBond c := by
  let atom := a.molecule.atoms.get (a.core c)
  have lookup : a.molecule.atoms[(a.core c).val]? = some atom := by simp [atom]
  have records := a.records (a.core c)
  rw [a.core_tag] at records
  have nonHydrogen : atom.element ≠ .H := by
    intro hydrogen
    exact nonH ((congrArg AtomSpec.element records).symm.trans hydrogen)
  have vals : RawMolecule.defaultValences atom = RawMolecule.defaultValences (coreAtom c) := by
    simpa using congrArg RawMolecule.defaultValences records
  obtain ⟨rest,head⟩ := List.head?_eq_some_iff.mp first
  apply selected_valence_planned_total a c admitted atom V lookup nonHydrogen unbracketed
  simp [vals,head,allowed]

/-- Mixed cores need only a common sufficient first native valence at each parent;
no per-parent completed-H equality is supplied. -/
theorem first_valence_totals_agree (a b : Completion coreAtom coreBond)
    (aAdmitted : a.molecule.Admissible) (bAdmitted : b.molecule.Admissible)
    (V : Fin k → Nat)
    (nonH : ∀ c, (coreAtom c).element ≠ .H)
    (first : ∀ c, (RawMolecule.defaultValences (coreAtom c)).head? = some (V c))
    (aUnbracketed : ∀ c, (a.molecule.atoms.get (a.core c)).explicitHydrogens? = none)
    (bUnbracketed : ∀ c, (b.molecule.atoms.get (b.core c)).explicitHydrogens? = none)
    (aAllowed : ∀ c, a.molecule.incidentBondOrderSum (a.core c).val ≤ V c)
    (bAllowed : ∀ c, b.molecule.incidentBondOrderSum (b.core c).val ≤ V c) (c : Fin k) :
    a.hydrogenCount c + (addedParents a.molecule).count (a.core c).val =
      b.hydrogenCount c + (addedParents b.molecule).count (b.core c).val := by
  rw [first_valence_planned_total a c aAdmitted (V c) (nonH c) (first c) (aUnbracketed c) (aAllowed c),
    first_valence_planned_total b c bAdmitted (V c) (nonH c) (first c) (bUnbracketed c) (bAllowed c)]

/-- Mixed native first-valence classes construct matched actual prepared graphs with
no all-carbon restriction and no supplied per-parent H-count equality. -/
theorem prepared_first_valence_bijection (a b : Completion coreAtom coreBond)
    (V : Fin k → Nat)
    (nonH : ∀ c, (coreAtom c).element ≠ .H)
    (first : ∀ c, (RawMolecule.defaultValences (coreAtom c)).head? = some (V c))
    (aUnbracketed : ∀ c, (a.molecule.atoms.get (a.core c)).explicitHydrogens? = none)
    (bUnbracketed : ∀ c, (b.molecule.atoms.get (b.core c)).explicitHydrogens? = none)
    (aAllowed : ∀ c, a.molecule.incidentBondOrderSum (a.core c).val ≤ V c)
    (bAllowed : ∀ c, b.molecule.incidentBondOrderSum (b.core c).val ≤ V c)
    {xyzA xyzB : SpatialConfiguration} {ra rb : RawMolecule × SpatialConfiguration}
    (acceptedA : prepare? a.molecule xyzA = some ra)
    (acceptedB : prepare? b.molecule xyzB = some rb) :
    ∃ e : Fin ra.1.atomCount ≃ Fin rb.1.atomCount,
      (∀ c, (e ⟨(a.core c).val,lt_of_lt_of_le (a.core c).isLt
        (prepare?_certified acceptedA).atomCount_le⟩).val = (b.core c).val) ∧
      (∀ v, heavyCore (rb.1.atoms.get (e v)) = heavyCore (ra.1.atoms.get v)) ∧
      (∀ v w, rb.1.bondOrder (e v).val (e w).val = ra.1.bondOrder v.val w.val) := by
  apply prepared_spellings_bijection a b acceptedA acceptedB
  exact first_valence_totals_agree a b (prepare?_certified acceptedA).input_admissible.1
    (prepare?_certified acceptedB).input_admissible.1 V nonH first aUnbracketed bUnbracketed aAllowed bAllowed

assert_kernel_only prepared_first_valence_bijection
assert_kernel_only missing_selected_valence
assert_kernel_only selected_valence_planned_total
assert_kernel_only first_valence_planned_total
assert_kernel_only first_valence_totals_agree
assert_kernel_only native_incident_eq_graph_sum
assert_kernel_only unbracketed_carbon_planned_total
assert_kernel_only ordinary_carbon_totals_agree
assert_kernel_only prepared_ordinary_carbon_bijection
assert_kernel_only unbracketed_carbon_planned_total_of_native_sum
assert_kernel_only bondSum_decomposition
assert_kernel_only missing_unbracketed_carbon
assert_kernel_only unbracketed_carbon_total_of_native_sum
end TetraStereo.OneCenter.OrdinaryHydrogenSpellings.Production
