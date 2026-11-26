import TetraStereo.Engine.RingChemicalRenumbering
import TetraStereo.Engine.RingHydrogenValenceCounts
import TetraStereo.Engine.RingHydrogenSpellingGeometry

/-! Raw molecular reports for ordinary hydrogen spellings and their physical placements. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter
open LocalizedChemicalRing (Input)
open RingRawRenumbering (AtomMap MolecularRecord molecularRecord)
open RingNumberedHydrogenGeometry (withSourceGeometry reindexed reindexed_lookup_image native_eq)
open RingHydrogenCompletion (heavyCore plan)
open RingWrittenPHReadings (PhysicalAgreement)
variable {i j : Input}

/-- Bonds and molecular atom data after materialization, independently of the coordinate tables. -/
structure GraphMap (i j : Input) where
  atoms : i.certified.Atom ≃ j.certified.Atom
  records : ∀ a, (j.molecule.atoms[(atoms a).val]?).map molecularRecord =
    (i.molecule.atoms[a.val]?).map molecularRecord
  bonds : ∀ a b, j.molecule.bondOrder (atoms a).val (atoms b).val = i.molecule.bondOrder a.val b.val

/-- A request uses the original IDs on each side. Preserve invalid IDs for rejections. -/
def moveId {n m : Nat} (e : Fin n ≃ Fin m) (a : Nat) : Nat :=
  if h : a < n then (e ⟨a,h⟩).val else a

@[simp] theorem moveId_val {n m : Nat} (e : Fin n ≃ Fin m) (a : Fin n) :
    moveId e a.val = (e a).val := by simp [moveId,a.isLt]

def GraphMap.atSourceGeometry (g : GraphMap i j) : AtomMap i (withSourceGeometry i j g.atoms) where
  atoms := g.atoms
  records := g.records
  bonds := g.bonds
  positions := reindexed_lookup_image g.atoms

/-- All requests on two hydrogen-complete graphs agree when corresponding local physical
frames agree. The two coordinate tables may contain independently chosen rational points. -/
theorem closed_graph_report (g : GraphMap i j) (left : plan i.molecule = []) (right : plan j.molecule = [])
    (hands : PhysicalAgreement j j.spatial (reindexed i j g.atoms)) (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial (ids.map (moveId g.atoms)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map
        (List.map fun row => (moveId g.atoms row.1,row.2)) := by
  rw [←native_eq g.atoms right hands]
  exact RingReportRenumber.closed_raw_report g.atSourceGeometry left right ids

/-- Transport the public calls on the original sources through both actual preparations. -/
theorem prepared_graph_report {s t : Input} (g : GraphMap i j)
    (gs : LocalizedChemicalRing.coordinatesAdmitted s = true) (gt : LocalizedChemicalRing.coordinatesAdmitted t = true)
    (left : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (right : RingHydrogenCompletion.prepare? t.molecule t.spatial = some (j.molecule,j.spatial))
    (fixed : RingPyramidalChoices.sites s.molecule s.spatial i.molecule i.spatial = [])
    (fixed' : RingPyramidalChoices.sites t.molecule t.spatial j.molecule j.spatial = [])
    (hands : PhysicalAgreement j j.spatial (reindexed i j g.atoms)) (ids : List Nat)
    (bs : ∀ n ∈ ids, n < s.molecule.atomCount) (bt : ∀ n ∈ ids.map (moveId g.atoms), n < t.molecule.atomCount) :
    RingHydrogenReport.fromRaw? t.molecule t.spatial (ids.map (moveId g.atoms)) =
      (RingHydrogenReport.fromRaw? s.molecule s.spatial ids).map
        (List.map fun row => (moveId g.atoms row.1,row.2)) := by
  rw [RingHydrogenReport.fromRaw_materialized_eq (RingSpatialTransport.readmit t) gt right fixed' _ bt,
      RingHydrogenReport.fromRaw_materialized_eq (RingSpatialTransport.readmit s) gs left fixed _ bs]
  exact closed_graph_report g (RingHydrogenCompletion.prepare?_closed left)
    (RingHydrogenCompletion.prepare?_closed right) hands ids

open OrdinaryHydrogenSpellings (Completion)
variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

def rawVertices (i : Input) {m : RawMolecule} (h : i.molecule = m) :
    i.certified.Atom ≃ Fin m.atomCount :=
  finCongr ((i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1).trans (congrArg RawMolecule.atomCount h))

theorem record_at_rawVertex (i : Input) {m : RawMolecule} (h : i.molecule = m) (v : i.certified.Atom) :
    i.molecule.atoms[v.val]? = some (m.atoms.get (rawVertices i h v)) := by
  subst m
  exact List.getElem?_eq_getElem (rawVertices i rfl v).isLt

theorem rawVertex_bond (i : Input) {m : RawMolecule} (h : i.molecule = m) (v w : i.certified.Atom) :
    i.molecule.bondOrder v.val w.val = m.bondOrder (rawVertices i h v).val (rawVertices i h w).val := by
  subst m; rfl

/-- Construct the complete atom correspondence by matching terminal hydrogens at each parent. -/
noncomputable def ofHydrogenCounts (a b : Completion coreAtom coreBond)
    (src : i.molecule = a.molecule) (tgt : j.molecule = b.molecule)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) : GraphMap i j := by
  let e := a.atomEquiv b counts
  let f := ((rawVertices i src).trans e).trans (rawVertices j tgt).symm
  have matched (x : i.certified.Atom) : rawVertices j tgt (f x) = e (rawVertices i src x) := by simp [f]
  refine ⟨f,?_,?_⟩
  · intro v
    rw [record_at_rawVertex j tgt,record_at_rawVertex i src,matched]
    have h := congrArg molecularRecord (a.atomEquiv_records b counts (rawVertices i src v))
    exact congrArg some h
  · intro v w
    rw [rawVertex_bond j tgt,rawVertex_bond i src,matched,matched]
    exact a.atomEquiv_bonds b counts _ _

/-- Each heavy atom maps to its specified counterpart, regardless of the written atom indices. -/
theorem ofHydrogenCounts_core (a b : Completion coreAtom coreBond)
    (src : i.molecule = a.molecule) (tgt : j.molecule = b.molecule)
    (counts : ∀ p, a.hydrogenCount p = b.hydrogenCount p) (p : Fin k) :
    (ofHydrogenCounts a b src tgt counts).atoms ((rawVertices i src).symm (a.core p)) =
      (rawVertices j tgt).symm (b.core p) := by
  simp [ofHydrogenCounts,a.atomEquiv_core b counts]

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.ofHydrogenCounts
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.closed_graph_report
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.prepared_graph_report

namespace TetraStereo.Engine.RingSpellingPopulation
open OneCenter RingHydrogenCompletion RingPyramidalChoices
open RingGroupedReport (Report)
open LocalizedChemicalRing (Input)

/-- A placement family always contains at least one actual coordinate table. -/
theorem choices_nonempty (ss : List Site) (ps : List Point) : ∃ x, x ∈ choices ss ps := by
  induction ss generalizing ps with
  | nil => exact ⟨ps,by simp [choices]⟩
  | cons s ss ih =>
    obtain ⟨x,hx⟩ := ih (ps.set s.hydrogen s.plus)
    exact ⟨x,List.mem_append_left _ hx⟩

theorem option_map_injective {α β : Type} (F : α → β) (inj : Function.Injective F) :
    Function.Injective (Option.map F) := by
  intro a b eq
  cases a <;> cases b <;> simp_all
  exact inj eq

/-- Two finite placement populations give corresponding consensus results when
physical counterparts exist in both directions and each related pair transports.
A disagreement, missing observation or other outer failure is preserved. -/
theorem search_transport (left right : List Point → Option Report)
    (ls rs : List Site) (lp rp : List Point) (F : Report → Report) (inj : Function.Injective F)
    (R : List Point → List Point → Prop)
    (forth : ∀ x ∈ choices ls lp, ∃ y ∈ choices rs rp, R x y)
    (back : ∀ y ∈ choices rs rp, ∃ x ∈ choices ls lp, R x y)
    (observed : ∀ x ∈ choices ls lp, ∀ y ∈ choices rs rp, R x y → right y = (left x).map F) :
    RingHydrogenReport.search? right rs rp = (RingHydrogenReport.search? left ls lp).map F := by
  have forward {rows : Report} (got : RingHydrogenReport.search? left ls lp = some rows) :
      RingHydrogenReport.search? right rs rp = some (F rows) := by
    apply (RingHydrogenReport.search?_iff ..).mpr
    intro y hy
    obtain ⟨x,hx,rel⟩ := back y hy
    rw [observed x hx y hy rel,(RingHydrogenReport.search?_iff ..).mp got x hx]
    rfl
  have reverse {rows : Report} (got : RingHydrogenReport.search? right rs rp = some rows) :
      ∃ original, RingHydrogenReport.search? left ls lp = some original ∧ F original = rows := by
    obtain ⟨x,hx⟩ := choices_nonempty ls lp
    obtain ⟨y,hy,rel⟩ := forth x hx
    have eq := (observed x hx y hy rel).symm.trans ((RingHydrogenReport.search?_iff ..).mp got y hy)
    obtain ⟨original,ho,hr⟩ := Option.map_eq_some_iff.mp eq
    refine ⟨original,(RingHydrogenReport.search?_iff ..).mpr ?_,hr⟩
    intro u hu
    obtain ⟨v,hv,rel'⟩ := forth u hu
    apply option_map_injective F inj
    rw [←observed u hu v hv rel',(RingHydrogenReport.search?_iff ..).mp got v hv]
    simp [hr]
  cases hl : RingHydrogenReport.search? left ls lp with
  | some rows => exact forward hl
  | none =>
    cases hr : RingHydrogenReport.search? right rs rp with
    | none => rfl
    | some rows =>
      obtain ⟨original,got,_⟩ := reverse hr
      rw [hl] at got
      contradiction

/-- Renaming IDs throughout a report is injective whenever the ID map is injective. -/
theorem report_map_injective (rename : Nat → Nat) (inj : Function.Injective rename) :
    Function.Injective (List.map (fun row : Nat × Option RingNestedActivePair.Labels => (rename row.1,row.2))) := by
  apply List.map_injective_iff.mpr
  intro a b eq
  exact Prod.ext (inj (congrArg Prod.fst eq)) (by simpa only using congrArg (fun row => row.2) eq)

/-- Independent source preparations, including unresolved P–H placement choices,
transport their entire native raw response under a physically covering relation.
Only each related pair's observed response is transported; consensus is derived. -/
theorem raw_population_transport
    {m out m' out' : RawMolecule} {g pos g' pos' : SpatialConfiguration} {source target : Input}
    (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (ht : LocalizedChemicalRing.admitRawSpatial? m' g' = some target)
    (gs : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (gt : LocalizedChemicalRing.coordinatesAdmitted target = true)
    (done : prepare? m g = some (out,pos)) (done' : prepare? m' g' = some (out',pos'))
    (ids ids' : List Nat) (bs : ∀ n ∈ ids, n < m.atomCount) (bt : ∀ n ∈ ids', n < m'.atomCount)
    (F : Report → Report) (inj : Function.Injective F)
    (R : SpatialConfiguration → SpatialConfiguration → Prop)
    (forth : ∀ x ∈ variants m g out pos, ∃ y ∈ variants m' g' out' pos', R x y)
    (back : ∀ y ∈ variants m' g' out' pos', ∃ x ∈ variants m g out pos, R x y)
    (observed : ∀ x ∈ variants m g out pos, ∀ y ∈ variants m' g' out' pos', R x y →
      RingHydrogenReport.fromRaw? out' y ids' = (RingHydrogenReport.fromRaw? out x ids).map F) :
    RingHydrogenReport.fromRaw? m' g' ids' = (RingHydrogenReport.fromRaw? m g ids).map F := by
  rw [RingSpatialTransport.public_search hs gs done ids bs,
    RingSpatialTransport.public_search ht gt done' ids' bt]
  apply search_transport _ _ _ _ _ _ F inj (fun x y => R ⟨x⟩ ⟨y⟩)
  · intro x hx
    obtain ⟨y,hy,rel⟩ := forth ⟨x⟩ (List.mem_map.mpr ⟨x,hx,rfl⟩)
    obtain ⟨yp,hyp,rfl⟩ := List.mem_map.mp hy
    exact ⟨yp,hyp,rel⟩
  · intro y hy
    obtain ⟨x,hx,rel⟩ := back ⟨y⟩ (List.mem_map.mpr ⟨y,hy,rfl⟩)
    obtain ⟨xp,hxp,rfl⟩ := List.mem_map.mp hx
    exact ⟨xp,hxp,rel⟩
  · intro x hx y hy rel
    have eq := observed ⟨x⟩ (List.mem_map.mpr ⟨x,hx,rfl⟩) ⟨y⟩ (List.mem_map.mpr ⟨y,hy,rfl⟩) rel
    simpa only [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done),
      RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done')] using eq

end TetraStereo.Engine.RingSpellingPopulation
assert_kernel_only TetraStereo.Engine.RingSpellingPopulation.search_transport
assert_kernel_only TetraStereo.Engine.RingSpellingPopulation.raw_population_transport

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingHydrogenCompletion RingPyramidalChoices
open LocalizedChemicalRing (Input)
open RingSpatialTransport (atGeometry size full_original)
open RingWrittenPHReadings (CanonicalPhysicalAgreement canonicalPhysicalAgreement_iff)
open RingNumberedHydrogenGeometry (reindexed)
variable {i j : Input}

private theorem moveId_symm {n m : Nat} (e : Fin n ≃ Fin m) (a : Nat) :
    moveId e.symm (moveId e a) = a := by
  have sz : n = m := by simpa using Fintype.card_congr e
  by_cases h : a < n
  · let v : Fin n := ⟨a,h⟩
    change moveId e.symm (moveId e v.val) = v.val
    simp
  · have h' : ¬ a < m := by omega
    simp [moveId,h,h']

theorem moveId_injective {n m : Nat} (e : Fin n ≃ Fin m) : Function.Injective (moveId e) :=
  Function.LeftInverse.injective (moveId_symm e)

def GraphMap.atTables (g : GraphMap i j) (x y : SpatialConfiguration)
    (lx : x.positions.length = size i) (ly : y.positions.length = size j) :
    GraphMap (atGeometry i x lx) (atGeometry j y ly) :=
  ⟨g.atoms,g.records,g.bonds⟩

/-- Reindex a full coordinate table into the target numbering and compare one
actual signed reading per geometric center, including degenerate readings. -/
def ReadingMatch (g : GraphMap i j) (x y : SpatialConfiguration) : Prop :=
  ∃ lx : x.positions.length = size i, CanonicalPhysicalAgreement j y (reindexed (atGeometry i x lx) j g.atoms)

theorem closed_placements (g : GraphMap i j) (x y : SpatialConfiguration)
    (ly : y.positions.length = size j) (matchFrames : ReadingMatch g x y)
    (left : plan i.molecule = []) (right : plan j.molecule = []) (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule y (ids.map (moveId g.atoms)) =
      (RingHydrogenReport.fromRaw? i.molecule x ids).map (List.map fun row => (moveId g.atoms row.1,row.2)) := by
  obtain ⟨lx,hands⟩ := matchFrames
  apply closed_graph_report (g.atTables x y lx ly) left right _ ids
  exact (canonicalPhysicalAgreement_iff ..).mp hands

/-- The native raw consensus for two independent P–H placement families. Only
signed molecular frames are compared between families. The result covers
agreement, refusal and disagreement on the whole requested list. -/
theorem population_graph_report {s t : Input} (g : GraphMap i j)
    (gs : LocalizedChemicalRing.coordinatesAdmitted s = true) (gt : LocalizedChemicalRing.coordinatesAdmitted t = true)
    (left : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (right : prepare? t.molecule t.spatial = some (j.molecule,j.spatial))
    (forth : ∀ x ∈ variants s.molecule s.spatial i.molecule i.spatial,
      ∃ y ∈ variants t.molecule t.spatial j.molecule j.spatial, ReadingMatch g x y)
    (back : ∀ y ∈ variants t.molecule t.spatial j.molecule j.spatial,
      ∃ x ∈ variants s.molecule s.spatial i.molecule i.spatial, ReadingMatch g x y)
    (ids : List Nat) (bs : ∀ n ∈ ids, n < s.molecule.atomCount)
    (bt : ∀ n ∈ ids.map (moveId g.atoms), n < t.molecule.atomCount) :
    RingHydrogenReport.fromRaw? t.molecule t.spatial (ids.map (moveId g.atoms)) =
      (RingHydrogenReport.fromRaw? s.molecule s.spatial ids).map (List.map fun row => (moveId g.atoms row.1,row.2)) := by
  apply RingSpellingPopulation.raw_population_transport (RingSpatialTransport.readmit s) (RingSpatialTransport.readmit t)
    gs gt left right _ _ bs bt _ (RingSpellingPopulation.report_map_injective _ (moveId_injective g.atoms))
    (ReadingMatch g) forth back
  intro x hx y hy hm
  exact closed_placements g x y ((variants_positions_length hy).trans (full_original j)) hm
    (prepare?_closed left) (prepare?_closed right) ids
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.population_graph_report

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingHydrogenCompletion RingPyramidalChoices OrdinaryHydrogenSpellings
open OrdinaryHydrogenSpellings.Production (producedCompletion produced_hydrogenCount)
open LocalizedChemicalRing (Input)
variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

/-- The two public admissions and preparations are ordinary execution witnesses. Only
the original graph is annotated with heavy vertices and their terminal H neighbors. -/
structure PreparedSpelling (a : Completion coreAtom coreBond) where
  source : Input
  raw : source.molecule = a.molecule
  coordinates : LocalizedChemicalRing.coordinatesAdmitted source = true
  result : Input
  prepared : prepare? source.molecule source.spatial = some (result.molecule,result.spatial)

def PreparedSpelling.certificate {a : Completion coreAtom coreBond} (s : PreparedSpelling a) :
    Certified a.molecule s.source.spatial s.result.molecule s.result.spatial :=
  prepare?_certified (s.raw ▸ s.prepared)

noncomputable def totalH (a : Completion coreAtom coreBond) (p : Fin k) :=
  a.hydrogenCount p + missing a.molecule (a.core p).val

noncomputable def preparedMap {a b : Completion coreAtom coreBond} (s : PreparedSpelling a) (t : PreparedSpelling b)
    (counts : ∀ p, totalH a p = totalH b p) : GraphMap s.result t.result :=
  ofHydrogenCounts (producedCompletion s.certificate) (producedCompletion t.certificate) rfl rfl (fun p => by
    rw [produced_hydrogenCount,produced_hydrogenCount,addedParents_count _ _ (a.core p).isLt,
      addedParents_count _ _ (b.core p).isLt]
    exact counts p)

theorem preparedMap_core {a b : Completion coreAtom coreBond} (s : PreparedSpelling a) (t : PreparedSpelling b)
    (counts : ∀ p, totalH a p = totalH b p) (p : Fin k) :
    moveId (preparedMap s t counts).atoms (a.core p).val = (b.core p).val := by
  let x := (rawVertices s.result rfl).symm ((producedCompletion s.certificate).core p)
  change moveId (preparedMap s t counts).atoms x.val = _
  rw [moveId_val]
  exact congrArg Fin.val (ofHydrogenCounts_core (producedCompletion s.certificate)
    (producedCompletion t.certificate) rfl rfl _ p)

/-- The entire native report follows from the shared heavy core, per-parent ordinary
H totals of the source spellings, and coverage of actual signed frames in both
placement families. No atom correspondence on the completed graphs is supplied. -/
theorem spelling_report {a b : Completion coreAtom coreBond} (s : PreparedSpelling a) (t : PreparedSpelling b)
    (counts : ∀ p, totalH a p = totalH b p)
    (forth : ∀ x ∈ variants s.source.molecule s.source.spatial s.result.molecule s.result.spatial,
      ∃ y ∈ variants t.source.molecule t.source.spatial t.result.molecule t.result.spatial,
        ReadingMatch (preparedMap s t counts) x y)
    (back : ∀ y ∈ variants t.source.molecule t.source.spatial t.result.molecule t.result.spatial,
      ∃ x ∈ variants s.source.molecule s.source.spatial s.result.molecule s.result.spatial,
        ReadingMatch (preparedMap s t counts) x y)
    (parents : List (Fin k)) :
    RingHydrogenReport.fromRaw? t.source.molecule t.source.spatial (parents.map fun p => (b.core p).val) =
      (RingHydrogenReport.fromRaw? s.source.molecule s.source.spatial (parents.map fun p => (a.core p).val)).map
        (List.map fun row => (moveId (preparedMap s t counts).atoms row.1,row.2)) := by
  have ids : (parents.map fun p => (a.core p).val).map (moveId (preparedMap s t counts).atoms) =
      parents.map fun p => (b.core p).val := by simp [List.map_map,Function.comp_def,preparedMap_core]
  have bounds (x : Completion coreAtom coreBond) (prep : PreparedSpelling x) :
      ∀ n ∈ parents.map (fun p => (x.core p).val), n < prep.source.molecule.atomCount := by
    intro n hn
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hn
    rw [prep.raw]
    exact (x.core p).isLt
  rw [←ids]
  exact population_graph_report (preparedMap s t counts) s.coordinates t.coordinates s.prepared t.prepared
    forth back _ (bounds a s) (ids ▸ bounds b t)
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.spelling_report

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter OrdinaryHydrogenSpellings OrdinaryHydrogenSpellings.Production
open RingPyramidalChoices (addedParents_count)
variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

/-- On an ordinary unbracketed carbon, the retained bond orders fix the sum of
written and implicit H even when the number of written H vertices changes. -/
theorem totalH_carbon {a : Completion coreAtom coreBond} (s : PreparedSpelling a) (p : Fin k)
    (carbon : OrdinaryCarbonAt a p) : totalH a p = 4 - heavyBondSum coreBond p := by
  obtain ⟨atom,lookup,element,aliphatic,_,unbracketed,allowed⟩ := carbon
  exact unbracketed_carbon_total_of_native_sum a p atom lookup element aliphatic unbracketed
    (native_incident_eq_graph_sum _ s.certificate.input_admissible.1 _) allowed

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.totalH_carbon

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingActivePairs RingActiveDistanceSchedule RingPyramidalPublication
open RingEligibleGraph RingReportRenumber RingSpatialTransport RingFrameTransport
open RingWrittenPHReadings RingNumberedHydrogenGeometry
open LocalizedChemicalRing (Input)

abbrev sphereEntry (i : Input) (root : i.certified.Atom) (k : Nat) (q : Site i) :=
  storedEntry (RingSphereQueue.stored (publish i) root (queue i (eligible i) root) (height i) k) q

/-- Exact optional entry, including absence, in the evaluator's materialized queue. -/
theorem sphereEntry_exact (i : Input) (root : i.certified.Atom) (k : Nat)
    (bound : k ≤ height i + 1) (q : Site i) :
    sphereEntry i root k q = if candidate (eligible i) root q ∧ height i < distance q + k
      then some (RingChemicalGraphProof.state i q) else none := by
  have pres : storedPresent (RingSphereQueue.stored (publish i) root (queue i (eligible i) root) (height i) k) q ↔
      candidate (eligible i) root q ∧ height i < distance q + k := by
    induction k with
    | zero => simp [RingSphereQueue.stored,storedPresent,Nat.not_lt_of_ge (distance_bound q)]
    | succ k ih =>
      rw [storedPresent_succ, inventory, ih (by omega)]
      have := distance_bound q
      constructor
      · rintro (⟨h,depth⟩ | ⟨h,depth⟩) <;> exact ⟨h,by omega⟩
      · rintro ⟨h,depth⟩
        by_cases later : height i < distance q + k
        · exact Or.inr ⟨h,later⟩
        · exact Or.inl ⟨h,by omega⟩
  have val := congrFun (RingSphereQueue.stored_eq (publish i) root (queue i (eligible i) root) k) q
  rw [run_exact (RingChemicalGraphProof.skips i) (inventory i (eligible i) root) k bound] at val
  change (sphereEntry i root k q).getD (some none) = _ at val
  have isWritten := (storedEntry_presence _ q).trans pres
  change (sphereEntry i root k q).isSome = true ↔ _ at isWritten
  cases he : sphereEntry i root k q with
  | none =>
    rw [he] at isWritten
    rw [if_neg (fun h => by simpa using isWritten.mpr h)]
  | some v =>
    rw [he] at isWritten val
    have h := isWritten.mp rfl
    rw [if_pos h] at val ⊢
    exact congrArg some val

private theorem reindexed_height (i : Input) (x : SpatialConfiguration) (full : x.positions.length = size i) :
    height (atGeometry i x full) = height i := by
  let e := reindexSite i x full
  have d (q : Site i) : distance (e q) = distance q := rfl
  have upper {a b : Input} (f : Site a → Site b) (depth : ∀ q, distance (f q) = distance q) : height a ≤ height b := by
    have all (qs : List (Site a)) : qs.foldr (fun q n => max (distance q) n) 0 ≤ height b := by
      induction qs with
      | nil => exact Nat.zero_le _
      | cons q qs ih => exact max_le (by rw [←depth q]; exact distance_bound _) ih
    exact all _
  exact Nat.le_antisymm (upper e.symm (fun q => by simpa using (d (e.symm q)).symm)) (upper e d)

/-- Replacing coordinates by independently chosen positions with the same local
physical readings preserves the actual cell written at each occurrence in every sphere. -/
theorem sphereEntry_coordinates (i : Input) (x : SpatialConfiguration) (full : x.positions.length = size i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (hands : PhysicalAgreement i i.spatial x)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    sphereEntry (atGeometry i x full) root k (reindexSite i x full q) = sphereEntry i root k q := by
  let j := atGeometry i x full
  have gj := (coordinates_of_physicalAgreement i x full hands).trans geom
  have same : RingChemicalGraphProof.state j (reindexSite i x full q) = RingChemicalGraphProof.state i q := by
    rw [←stateG_input gj,←stateG_input geom,inputGeometry_eq i,inputGeometry_eq j]
    change stateG j (geometry x) (reindexSite i x full q) = stateG i (geometry i.spatial) q
    rw [stateG_reindex]
    exact (stateG_transport q (fun u _ => RingPhysicalFrameBridge.siteAgree hands u)).symm
  rw [sphereEntry_exact _ _ _ (by rw [reindexed_height]; exact bound),sphereEntry_exact i root k bound,
    reindexed_height,same]
  rfl

/-- The native sphere store for two graph spellings and independent coordinate tables.
Only one canonical physical reading per center is required. -/
theorem graph_sphereEntry {i j : Input} (g : GraphMap i j)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (hands : CanonicalPhysicalAgreement j j.spatial (reindexed i j g.atoms))
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    sphereEntry i root k q = sphereEntry j (g.atoms root) k
      ((reindexSite j (reindexed i j g.atoms) (reindexed_full _)).symm
        (RingRawRenumbering.AtomMap.site g.atSourceGeometry q)) := by
  let x := reindexed i j g.atoms
  let e := reindexSite j x (reindexed_full _)
  let r := g.atSourceGeometry
  have hp := (canonicalPhysicalAgreement_iff ..).mp hands
  have gj := (coordinatesAdmitted_eq g.atoms hp).symm.trans (RingRawRenumbering.AtomMap.coordinates r geom)
  have ht := (schedule_height r).trans (reindexed_height j x (reindexed_full _))
  have h := sphereEntry_coordinates j x (reindexed_full _) gj hp (g.atoms root) k (ht ▸ bound)
    (e.symm (RingRawRenumbering.AtomMap.site r q))
  change sphereEntry (withSourceGeometry i j g.atoms) _ _ (e (e.symm _)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact (chemical_stored_entry r geom root k bound q).trans h
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.graph_sphereEntry

namespace TetraStereo.Engine.RingHydrogenSpelling
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (distance height)
open RingGraphPaths (Path Represents)
open RingPyramidalPublication (eligible)
open RingNestedActivePair (Labels)

/-- Exactly the entries written by the public auxiliary queue after `k` spheres.
The right side uses a simple bonded path, its endpoint's eligibility and a
recursive chemical derivation for this occurrence. `v = none` is a written refusal. -/
theorem sphereEntry_iff_derives {i : Input} (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) (v : Option Labels) :
    sphereEntry i r k q = some (some v) ↔
      ∃ h a, ∃ p : Path i r h a, Represents q r h a ∧ a ≠ r ∧ eligible i a = true ∧
        height i + 1 < h.length + k ∧ RingEligibleGraph.Derives (eligible i) (RingChemicalGraphProof.Local i) r p v := by
  rw [sphereEntry_exact i r k bound]
  constructor
  · intro written
    split at written
    · rename_i met
      obtain ⟨⟨on,other,real,a,current,allowed⟩,deep⟩ := met
      obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
      obtain rfl := Option.some.inj (hb.symm.trans current)
      have p : Path i r q.val.node.history b := on ▸ path
      have rep : Represents q r q.val.node.history b := ⟨on,rfl,real,hb⟩
      have len := RingGraphPaths.path_length rep
      refine ⟨_,b,p,rep,fun e => other (hb.trans (congrArg some e)),allowed,by omega,?_⟩
      apply (RingChemicalGraphProof.path_iff valid p v).mp
      rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep]
      exact Option.some.inj written
    · contradiction
  · rintro ⟨h,a,p,rep,other,allowed,deep,deriv⟩
    have len := RingGraphPaths.path_length rep
    have cand : RingEligibleGraph.candidate (eligible i) r q :=
      ⟨rep.1,fun eqn => other (Option.some.inj (rep.2.2.2.symm.trans eqn)),rep.2.2.1,a,rep.2.2.2,allowed⟩
    rw [if_pos ⟨cand,by omega⟩,← RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep,
      (RingChemicalGraphProof.path_iff valid p v).mpr deriv]

/-- At an admitted geometry there are no written computation failures. Each lookup
is either absent or holds a completed refusal or descriptor pair. -/
theorem sphereEntry_ne_failure {i : Input} (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    sphereEntry i r k q ≠ some none := by
  rw [sphereEntry_exact i r k bound]
  obtain ⟨v,hv,_⟩ := RingChemicalGraphProof.total valid q
  split <;> simp [hv]

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.sphereEntry_iff_derives
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.sphereEntry_ne_failure
