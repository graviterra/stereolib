import TetraStereo.Engine.RingSingleCycleOrigin
import TetraStereo.Engine.RingDuplicateScale
import TetraStereo.Engine.RingTerminalLigandOrder

/-! Re-sort every level of each constitutional ligand key using the distance
from an auxiliary focus to the duplicated real occurrence. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSingleCycleComparison
open OneCenter SimpleGraph
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingRetainedChemicalTrace (Key Observation observation? compareKeys)
open RingSingleCycleOrigin (originPath pathDistance)
open RingDuplicateScale (observation key)
open private build from TetraStereo.Engine.RingRetainedChemicalTrace
open private observed from TetraStereo.Engine.RingTerminalLigandOrder

def native (i : Input) (q : Arm i) : Option Observation :=
  observation? i q (i.certified.executableLocalizedRerootChildren q).isEmpty

/-- Reserve zero for a real node and rank closer closure origins higher.
Both paths in the retained tree have at most atomCount vertices. -/
def weight (i : Input) (focus origin : List i.certified.Atom) : Nat :=
  1 + (2 * i.molecule.atomCount - pathDistance focus origin)

def active (i : Input) (focus : List i.certified.Atom) (q : Arm i) : Option Observation :=
  (native i q).map fun o => match q.occurrence.val.node.provenance with
    | .ringDuplicate d => {o with duplicate := weight i focus (originPath q.occurrence.val.node d)}
    | _ => o

private def binary (i : Input) (q : Arm i) : Option Observation :=
  (native i q).map fun o => {o with duplicate := if o.duplicate = 0 then 0 else 1}

def rebuilt (i : Input) (f : Site i) (q : Arm i) : Option Key :=
  RingDuplicateScale.build (active i f.val.node.history.reverse) i.certified.executableLocalizedRerootChildren
    (2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1) q

/-- Share one root-slice child index between all nodes of this reranked ligand. -/
private def indexed (i : Input) (f : Site i) (q : Arm i) : Option Key :=
  let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache
    (i.certified.localizedRerootCarrierCache (i.certified.certified.input.molecule.atomCount + 1))
    q.occurrence.val.root
  let children := fun c : Arm i => (slice.reader.readChildren c).getD []
  let focus := f.val.node.history.reverse
  let observe := fun c : Arm i => (observation? i c (children c).isEmpty).map fun o =>
    match c.occurrence.val.node.provenance with
    | .ringDuplicate d => {o with duplicate := weight i focus (originPath c.occurrence.val.node d)}
    | _ => o
  RingDuplicateScale.build observe children (2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1) q

@[csimp] private theorem indexed_exact : @rebuilt = @indexed := by
  funext i f q
  unfold indexed
  simp only [CertifiedLocalizedCIPInput.LocalizedRerootChildReader.readChildren_eq]
  rfl

private theorem native_build (i : Input) (n : Nat) (q : Arm i) :
    RingDuplicateScale.build (native i) i.certified.executableLocalizedRerootChildren n q =
      build i i.certified.executableLocalizedRerootChildren n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have ihfun := funext ih
    simp only [RingDuplicateScale.build,build,native]
    rw [ihfun]

/-- Root-preserving recursion only observes readers on its own original graph
slice. The statement also preserves the outcome of a failed lookup. -/
private theorem congr_build (i : Input) (r : i.certified.Atom) (x y : Arm i → Option Observation)
    (same : ∀ q, q.occurrence.val.root = r → x q = y q)
    (n : Nat) (q : Arm i) (on : q.occurrence.val.root = r) :
    RingDuplicateScale.build x i.certified.executableLocalizedRerootChildren n q =
      RingDuplicateScale.build y i.certified.executableLocalizedRerootChildren n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingDuplicateScale.build,same q on]
    have kids : (i.certified.executableLocalizedRerootChildren q).mapM
        (RingDuplicateScale.build x i.certified.executableLocalizedRerootChildren n) =
        (i.certified.executableLocalizedRerootChildren q).mapM
        (RingDuplicateScale.build y i.certified.executableLocalizedRerootChildren n) := by
      apply RingFrameTransport.mapM_congr_mem
      intro t mem
      exact ih t ((i.certified.localizedRerootChildren_root_eq _ _ _
        (i.certified.executableLocalizedRerootChildren_declarative _) mem).trans on)
    rw [kids]

/-- Every closure in this original-root slice has the same retained origin. -/
def CommonOrigin (i : Input) (r : i.certified.Atom) : Prop :=
  ∀ (q p : Arm i) (d e : Nat), q.occurrence.val.root = r → p.occurrence.val.root = r →
    q.occurrence.val.node.provenance = .ringDuplicate d →
    p.occurrence.val.node.provenance = .ringDuplicate e →
    originPath q.occurrence.val.node d = originPath p.occurrence.val.node e ∧ d = e

private theorem factors {i : Input} (focus : List i.certified.Atom)
    (r : i.certified.Atom) (common : CommonOrigin i r) :
    ∃ a b : Nat, 0 < a ∧ 0 < b ∧ ∀ q : Arm i, q.occurrence.val.root = r →
      native i q = (binary i q).map (observation (· * a)) ∧
      active i focus q = (binary i q).map (observation (· * b)) := by
  classical
  let hit := ∃ (q : Arm i) (d : Nat) (o : Observation), q.occurrence.val.root = r ∧
    q.occurrence.val.node.provenance = .ringDuplicate d ∧ native i q = some o
  have realOnly (q : Arm i) (o : Observation) (read : native i q = some o)
      (real : q.occurrence.val.node.provenance = .realAtom) (a b : Nat) :
      native i q = (binary i q).map (observation (· * a)) ∧
      active i focus q = (binary i q).map (observation (· * b)) := by
    have zero := (RingRetainedChemicalTrace.real_source real read).1
    cases o
    simp_all [active,binary,observation]
  by_cases existsHit : hit
  · obtain ⟨p,d,o,pr,pd,po⟩ := existsHit
    let a := i.molecule.atomCount + 1 - d
    let b := weight i focus (originPath p.occurrence.val.node d)
    have bound := (observed po).2 d pd
    refine ⟨a,b,by dsimp [a]; omega,by simp [b,weight],?_⟩
    intro q qr
    cases read : native i q with
    | none => simp [binary,active,read]
    | some u =>
      rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single q.occurrence with real | ⟨e,dup⟩
      · simpa only [read] using realOnly q u read real a b
      · obtain ⟨origin,idx⟩ := common q p e d qr pr dup pd
        have value := (observed read).1
        rw [dup] at value
        change u.duplicate = i.molecule.atomCount + 1 - e at value
        have pos : 0 < u.duplicate := by omega
        cases u
        simp_all [binary,active,observation,b,a]
        omega
  · refine ⟨1,1,by decide,by decide,?_⟩
    intro q qr
    cases read : native i q with
    | none => simp [binary,active,read]
    | some u =>
      rcases i.certified.carrierOccurrence_provenance_simple_or_ring i.single q.occurrence with real | ⟨e,dup⟩
      · simpa only [read] using realOnly q u read real 1 1
      · exact (existsHit ⟨q,e,u,qr,dup,read⟩).elim

/-- Compare any two directions after recomputing both ligand trees from the
active-focus observations. Ties and both strict directions agree with the
public constitutional table whenever this original-root slice has a common closure origin. -/
theorem of_common_origin {i : Input} (f : Site i)
    (common : CommonOrigin i f.val.root)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let u ← rebuilt i f ⟨x.val,some f⟩
        let v ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys u v)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y := by
  obtain ⟨a,b,ha,hb,reads⟩ := factors f.val.node.history.reverse f.val.root common
  let n := 2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1
  let cs := i.certified.executableLocalizedRerootChildren (fuel := i.certified.certified.input.molecule.atomCount+1)
  have scale (v : Nat) (pos : 0 < v) (reader : Arm i → Option Observation)
      (same : ∀ q : Arm i, q.occurrence.val.root = f.val.root →
        reader q = (binary i q).map (observation (· * v)))
      (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
      RingDuplicateScale.build reader cs n q = (RingDuplicateScale.build (binary i) cs n q).map (key (· * v)) := by
    exact (congr_build i f.val.root _ _ same n q on).trans
      (RingDuplicateScale.build_natural (fun _ _ h => Nat.mul_lt_mul_of_pos_right h pos) _ _ _ _)
  have arm (z : RingRetainedChemicalPreorder.Direction i f) :
      ∃ k, RingRetainedChemicalPreorder.keyFor z = key (· * a) k ∧
        rebuilt i f ⟨z.val,some f⟩ = some (key (· * b) k) := by
    let q : Arm i := ⟨z.val,some f⟩
    have orig := scale a ha _ (fun t h => (reads t h).1) q z.property.1
    have alt := scale b hb _ (fun t h => (reads t h).2) q z.property.1
    have known : RingDuplicateScale.build (native i) cs n q = some (RingRetainedChemicalPreorder.keyFor z) :=
      (native_build i n q).trans (RingRetainedChemicalPreorder.read_key z)
    rw [known] at orig
    cases found : RingDuplicateScale.build (binary i) cs n q with
    | none => simp [found] at orig
    | some k =>
      refine ⟨k,by simpa only [found,Option.map_some,Option.some.injEq] using orig,?_⟩
      exact alt.trans (by rw [found]; rfl)
  obtain ⟨k,kx,ax⟩ := arm x
  obtain ⟨l,ky,ay⟩ := arm y
  rw [RingRetainedChemicalPreorder.table_order, ← RingRetainedChemicalPreorder.compare_word]
  change (do let u ← rebuilt i f ⟨x.val,some f⟩
             let v ← rebuilt i f ⟨y.val,some f⟩
             pure (compareKeys u v)) = some (compareKeys _ _)
  rw [ax,ay]
  rw [kx,ky]
  change some (compareKeys (key (· * b) k) (key (· * b) l)) =
    some (compareKeys (key (· * a) k) (key (· * a) l))
  rw [RingDuplicateScale.compare_keys (fun _ _ h => Nat.mul_lt_mul_of_pos_right h ha),
    RingDuplicateScale.compare_keys (fun _ _ h => Nat.mul_lt_mul_of_pos_right h hb)]

/-- The unique-cycle support law supplies the common-origin hypothesis. -/
theorem all_ligands {i : Input} {c : i.certified.Atom}
    (cyc : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c)
    (one : RingCycleEntry.UniqueCycleSupport cyc) (f : Site i)
    (x y : RingRetainedChemicalPreorder.Direction i f) :
    (do let u ← rebuilt i f ⟨x.val,some f⟩
        let v ← rebuilt i f ⟨y.val,some f⟩
        pure (compareKeys u v)) =
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) x y := by
  apply of_common_origin f
  intro q p d e qr pr qd pd
  exact RingSingleCycleOrigin.common_origin cyc one q.occurrence p.occurrence
    (qr.trans pr.symm) qd pd

end TetraStereo.Engine.RingSingleCycleComparison
assert_kernel_only TetraStereo.Engine.RingSingleCycleComparison.all_ligands

assert_kernel_only TetraStereo.Engine.RingSingleCycleComparison.of_common_origin
