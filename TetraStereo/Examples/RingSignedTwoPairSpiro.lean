import TetraStereo.Engine.PublicAPI

set_option maxHeartbeats 7500000
set_option maxRecDepth 60000
set_option Elab.async false
set_option autoImplicit false
namespace TetraStereo.Examples.RingSignedTwoPairSpiro
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive
open CentresRingSpiroCasing (spatial)

/-- Replace the four fluorines of the five-carbon spiro scaffold by four
chlorodifluoromethyl groups. Each new carbon has an equivalent fluorine pair. -/
def molecule : RawMolecule where
  atoms := List.replicate 9 (.aliphatic .C) ++ List.replicate 4 (.aliphatic .H) ++
    (List.range 4).flatMap (fun _ => [.aliphatic .F,.aliphatic .F,.aliphatic .Cl])
  bonds := CentresRingSpiroCasing.molecule.bonds ++ (List.range 4).flatMap fun j =>
    (List.range 3).map fun k => ⟨5+j,13+3*j+k,.single⟩

def geometry : Geometry := fun i =>
  (spatial.positions ++ [⟨4,3,1⟩,⟨3,1,2⟩,⟨4,2,0⟩, ⟨4,-3,1⟩,⟨3,-1,2⟩,⟨4,-2,0⟩,
    ⟨-4,1,3⟩,⟨-3,2,1⟩,⟨-4,0,2⟩, ⟨-4,1,-3⟩,⟨-3,2,-1⟩,⟨-4,0,-2⟩])[i]?

def signedView {m g p} : RingAuxiliaryInventory.Result m g p → Option (Reading × List (List Nat))
  | .signedPaired s => some (s.reading,s.omitted)
  | _ => none

/-- A singly substituted route and a route around either three-membered ring
can reach the same carbon. All eight addresses remain in the result. -/
def omissions : List (List Nat) :=
  [[0,1,2,6],[0,1,5],[0,2,1,5],[0,2,6],[0,3,4,8],[0,3,7],[0,4,3,7],[0,4,8]]


open Promotion
private def target := canonicalCenterRoot 0
private def value (rev : Bool) (h : RS) : Reading := if rev then ⟨h.swap,h⟩ else ⟨h,h.swap⟩
private def atGeometry (rev : Bool) := if rev then mirror geometry else geometry

private def entries (rev : Bool) : InventoryPriority.Entries :=
  [([0,1],some (value rev .S)),([0,1,2],some (value rev .S)),([0,1,2,6],none),([0,1,5],none),
   ([0,2],some (value rev .R)),([0,2,1],some (value rev .R)),([0,2,1,5],none),([0,2,6],none),
   ([0,3],some (value rev .S)),([0,3,4],some (value rev .S)),([0,3,4,8],none),([0,3,7],none),
   ([0,4],some (value rev .R)),([0,4,3],some (value rev .R)),([0,4,3,7],none),([0,4,8],none)]

private def arm1 (rev : Bool) : Arm molecule target omissions where
  ligand := 1
  start := some ((molecule.canonicalChildren target)[0]'(by decide +kernel))
  bound := by decide +kernel
  facts := [([0,1],value rev .S),([0,1,2],value rev .S)]
  complete := by cases rev <;> decide +kernel

private def arm2 (rev : Bool) : Arm molecule target omissions where
  ligand := 2
  start := some ((molecule.canonicalChildren target)[1]'(by decide +kernel))
  bound := by decide +kernel
  facts := [([0,2],value rev .R),([0,2,1],value rev .R)]
  complete := by cases rev <;> decide +kernel

private def arm3 (rev : Bool) : Arm molecule target omissions where
  ligand := 3
  start := some ((molecule.canonicalChildren target)[2]'(by decide +kernel))
  bound := by decide +kernel
  facts := [([0,3],value rev .S),([0,3,4],value rev .S)]
  complete := by cases rev <;> decide +kernel

private def arm4 (rev : Bool) : Arm molecule target omissions where
  ligand := 4
  start := some ((molecule.canonicalChildren target)[3]'(by decide +kernel))
  bound := by decide +kernel
  facts := [([0,4],value rev .R),([0,4,3],value rev .R)]
  complete := by cases rev <;> decide +kernel

private def experiment (rev : Bool) : Experiment molecule [0] omissions where
  depth := 2
  domain := by decide +kernel
  focus := target
  reached := by decide +kernel
  center := by decide +kernel
  arms := [arm1 rev,arm2 rev,arm3 rev,arm4 rev]
  incident := by rfl
  four := rfl
  distinct := by decide +revert +kernel

/-- The side reached through bonds 0–1 and 0–2, including every terminal
atom of the two substituents on that ring. -/
def firstRing (i : Nat) : Bool := [1,2,5,6,9,10,13,14,15,16,17,18].contains i

theorem bond_cut : TwoPairPriority.BondCut molecule 0 firstRing := by
  unfold TwoPairPriority.BondCut
  decide +kernel

private def promotedReading (rev : Bool) :=
  (TwoPairPriority.certify? (experiment rev) (atGeometry rev)).map (·.reading)
private def slots (rev : Bool) := if rev then [1,3,2,4] else [2,4,1,3]

private theorem found_partition (rev : Bool) :
    (TwoPairPriority.classify? (experiment rev)).map (fun c => c.partition.order) = some (slots rev) := by
  cases rev <;> decide +kernel

/-- Compute the unmarked slots and reference geometry. The molecular cut
forces the letter for all marks simultaneously on each presentation. -/
private theorem promoted (rev : Bool) : promotedReading rev = some (value rev .S) := by
  have found := found_partition rev
  unfold promotedReading TwoPairPriority.certify?
  cases hc : TwoPairPriority.classify? (experiment rev) with
  | none => simp [hc] at found
  | some c =>
    have order : c.partition.order = slots rev := by simpa [hc] using found
    have fresh : 0 ∉ (experiment rev).arms.map Arm.ligand := by cases rev <;> decide +kernel
    have both : ∀ color : Bool, ∃ i ∈ (experiment rev).arms.map Arm.ligand, firstRing i = color := by
      intro color
      cases color
      · exact ⟨3,by simp [experiment,arm1,arm2,arm3,arm4],rfl⟩
      · exact ⟨1,by simp [experiment,arm1,arm2,arm3,arm4],rfl⟩
    cases rev
    · change c.partition.order = [2,4,1,3] at order
      have base : readback? geometry [2,4,1,3] = some .S := by decide +kernel
      let s : TwoPairPriority.PopulationReading c geometry := ⟨.S,order ▸ base⟩
      obtain ⟨high,low⟩ := c.partition.split_by_cut bond_cut rfl fresh order both
      exact s.certificate_of_cut bond_cut rfl fresh order high low
    · change c.partition.order = [1,3,2,4] at order
      have base : readback? (mirror geometry) [1,3,2,4] = some .R := by decide +kernel
      let s : TwoPairPriority.PopulationReading c (mirror geometry) := ⟨.R,order ▸ base⟩
      obtain ⟨high,low⟩ := c.partition.split_by_cut bond_cut rfl fresh order both
      exact s.certificate_of_cut bond_cut rfl fresh order high low

private def children (rev : Bool) := RingAuxiliaryInventory.classify? molecule (atGeometry rev)
  (fun _ => none) (fun _ => 2) (molecule.atomCount+1)

private theorem gathered (rev : Bool) :
    (RingAuxiliaryInventory.gatherSigned? (children rev) (RingAuxiliaryInventory.promotionPaths molecule target)).map
      RingAuxiliaryInventory.SignedInputs.entries = some (entries rev) := by
  cases rev <;> decide +kernel

private theorem made (rev : Bool) :
    RingAuxiliaryInventory.signedExperiment? 2 target (m := molecule) (p := [0])
      (by decide +kernel) (by rfl) (by decide +kernel) (entries rev) = some (experiment rev) := by
  cases rev <;> rfl

private theorem inventoryPerm (rev : Bool) : (TwoPairPriority.required (experiment rev)).Perm (entries rev) := by
  cases rev <;> decide +kernel

private theorem uniquePaths (rev : Bool) :
    ((TwoPairPriority.required (experiment rev)).map Prod.fst).Nodup := by cases rev <;> decide +kernel

/-- Each of the four eligible atom identifiers retains its geometric
reading in the public diagnosis, including with the eight omitted paths. -/
theorem diagnosed_votes (rev : Bool) :
    (inspectRingTwoPair? molecule (atGeometry rev) 0 2).bind RingTwoPairDiagnosis.votes? =
      some ([1,2,3,4].map (·,value rev .S)) := by
  have collect := gathered rev
  change ((RingAuxiliaryInventory.gatherSigned? (children rev)
    (RingAuxiliaryInventory.promotionPaths molecule target)).bind (fun inputs => do
      let e ← RingAuxiliaryInventory.inventoryExperiment? 2 target (m := molecule) (p := [0])
        (by decide +kernel) (by rfl) (by decide +kernel) inputs.entries
      if h : (TwoPairPriority.required e).Perm inputs.entries then
        if u : ((TwoPairPriority.required e).map Prod.fst).Nodup then
          return ⟨inputs,e,h,u,← TwoPairPriority.classify? e⟩
      none)).bind RingTwoPairDiagnosis.votes? = _
  cases got : RingAuxiliaryInventory.gatherSigned? (children rev)
      (RingAuxiliaryInventory.promotionPaths molecule target) with
  | none => simp [got] at collect
  | some ins =>
    obtain ⟨es,pos,neg⟩ := ins
    have equ : es = entries rev := by simpa [got] using collect
    subst es
    have prepared : RingAuxiliaryInventory.inventoryExperiment? 2 target (m := molecule) (p := [0])
        (by decide +kernel) (by rfl) (by decide +kernel) (entries rev) = some (experiment rev) := by
      cases rev <;> rfl
    simp only [Option.bind_some,Option.bind_eq_bind]
    rw [prepared]
    simp only [Option.bind_some,dif_pos (inventoryPerm rev),dif_pos (uniquePaths rev)]
    have accepted := promoted rev
    unfold promotedReading TwoPairPriority.certify? at accepted
    cases h : TwoPairPriority.classify? (experiment rev) with
    | none => simp [h] at accepted
    | some c =>
      simp only [h,Option.bind_eq_bind,Option.bind_some] at accepted
      exact c.votes_of_accepted accepted

private theorem signedProjection (rev : Bool) :
    (RingAuxiliaryInventory.signedPairedAt? [0] 2 (children rev)).bind signedView =
      some (value rev .S,omissions) := by
  have collect := gathered rev
  change ((RingAuxiliaryInventory.gatherSigned? (children rev)
    (RingAuxiliaryInventory.promotionPaths molecule target)).bind (fun inputs => do
      let e ← RingAuxiliaryInventory.signedExperiment? 2 target (m := molecule) (p := [0])
        (by decide +kernel) (by rfl) (by decide +kernel) inputs.entries
      return ← RingAuxiliaryInventory.finishSignedPaired? inputs e)).bind signedView = _
  cases got : RingAuxiliaryInventory.gatherSigned? (children rev)
      (RingAuxiliaryInventory.promotionPaths molecule target) with
  | none => simp [got] at collect
  | some ins =>
    obtain ⟨es,pos,neg⟩ := ins
    have equ : es = entries rev := by simpa [got] using collect
    subst es
    simp only [Option.bind_some,Option.bind_eq_bind]
    rw [made]
    simp only [Option.bind_some,RingAuxiliaryInventory.finishSignedPaired?,dif_pos (inventoryPerm rev),
      dif_pos (uniquePaths rev),Option.bind_eq_bind]
    have result := promoted rev
    unfold promotedReading at result
    cases hc : TwoPairPriority.certify? (experiment rev) (atGeometry rev) with
    | none => simp [hc] at result
    | some c =>
      have hand : c.reading = value rev .S := by simpa [hc] using result
      exact congrArg (fun v => some (v,omissions)) hand

private theorem constitutionalStops : (constitutionalOrder? molecule [0] 2).isNone = true := by decide +kernel
private theorem positivesStop (rev : Bool) :
    (RingAuxiliaryInventory.promotedAt? [0] 2 (children rev)).isNone = true := by cases rev <;> decide +kernel
private theorem singlePairStops (rev : Bool) :
    (RingAuxiliaryInventory.discoverAt? [0] 2 (children rev)).isNone = true := by cases rev <;> decide +kernel

def inspect (g : Geometry) :=
  (inspectRingOccurrence? molecule g [0] (molecule.atomCount+2) (fun _ => none) (fun _ => 2)).bind
    fun r => signedView r.val

private theorem public_center (rev : Bool) : inspect (atGeometry rev) = some (value rev .S,omissions) := by
  have dom : saturatedWithHalogens molecule = true := by decide +kernel
  have hc := Option.isNone_iff_eq_none.mp constitutionalStops
  have hp := Option.isNone_iff_eq_none.mp (positivesStop rev)
  have hd := Option.isNone_iff_eq_none.mp (singlePairStops rev)
  unfold inspect inspectRingOccurrence?
  simp only [dif_pos dom,Option.bind_eq_bind,Option.bind_assoc]
  change (RingAuxiliaryInventory.classifyAt? molecule (atGeometry rev) (fun _ => none)
      (fun _ => 2) (children rev) [0]).bind signedView = _
  simpa [RingAuxiliaryInventory.classifyAt?,hc,hp,hd] using signedProjection rev

theorem original_center : inspect geometry = some (⟨.S,.R⟩,omissions) := public_center false
theorem mirror_center : inspect (mirror geometry) = some (⟨.R,.S⟩,omissions) := public_center true

private def row (g : Geometry) (i : Nat) :=
  (RingCarbonReport.atCarbon? molecule g (molecule.atomCount+2) (fun _ => none) (fun _ => 2) i).map
    RingCarbonReport.Verdict.label

private theorem centerRow {g : Geometry} {v : Reading} (observed : inspect g = some (v,omissions)) :
    row g 0 = some v.label := by
  have domain : saturatedWithHalogens molecule = true := by decide +kernel
  unfold row
  rw [RingCarbonReport.atCarbon?_label_of_no_hydrogens domain (by decide +kernel) (by decide +kernel)]
  cases found : RingAuxiliaryInventory.classify? molecule g (fun _ => none) (fun _ => 2)
      (molecule.atomCount+2) [0] with
  | none => simp [inspect,inspectRingOccurrence?,domain,found] at observed
  | some r =>
    have hv : signedView r = some (v,omissions) := by
      simpa [inspect,inspectRingOccurrence?,domain,found] using observed
    cases r <;> simp [signedView] at hv
    simp [RingAuxiliaryInventory.Result.reading,hv.1]

private def labels (a b : RS) : List (Option LocalizedAuxiliaryLabel) :=
  [some (.chiral a),some (.chiral a),some (.chiral b),some (.chiral a),some (.chiral b),none,none,none,none]

private def census (a b : RS) := (List.range 9).map fun i => (i,(labels a b)[i]?.join)

private theorem fullReport (g : Geometry) (a b : RS)
    (allRows : ∀ i : Fin 9, row g i = some ((labels a b)[i.val]?.join)) :
    (classifyRingCarbonsAtBound? molecule g 2).map (·.labels) = some (census a b) := by
  have carbonIDs : RingCarbonReport.carbons molecule = List.range 9 := by decide +kernel
  have h := classifyRingCarbons?_labels_of_rows (m := molecule) (g := g) (fuel := molecule.atomCount+2)
    (hint := fun _ => none) (radius := fun _ => 2) (fun i => (labels a b)[i]?.join) (by decide +kernel)
    (fun i member => allRows ⟨i,List.mem_range.mp (carbonIDs ▸ member)⟩)
  rw [carbonIDs] at h
  exact h

/-- The central carbon and all four ring neighbors have uppercase letters.
The four chlorodifluoromethyl carbons have certified absences as fresh roots. -/
theorem original_report :
    (classifyRingCarbonsAtBound? molecule geometry 2).map (·.labels) = some (census .S .R) := by
  apply fullReport
  intro i
  fin_cases i
  · exact centerRow original_center
  all_goals decide +kernel

theorem mirror_report :
    (classifyRingCarbonsAtBound? molecule (mirror geometry) 2).map (·.labels) = some (census .R .S) := by
  apply fullReport
  intro i
  fin_cases i
  · exact centerRow mirror_center
  all_goals decide +kernel

end TetraStereo.Examples.RingSignedTwoPairSpiro

assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.original_center
assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.mirror_center
assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.original_report
assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.mirror_report

assert_kernel_only TetraStereo.Examples.RingSignedTwoPairSpiro.diagnosed_votes
