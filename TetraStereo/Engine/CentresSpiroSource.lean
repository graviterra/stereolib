import TetraStereo.Engine.CentresRing

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.SpiroSource

open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (Geometry readback?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-! P-93.5.3.2, Example 2. This checker is specific to the displayed Xabab
molecule with only the spiro configuration supplied. Both sorts before a choice
compare equivalent arms by element. After choosing an oxygen, the other
pair uses membership of that same oxygen in the branch. No auxiliary
configuration is available in this experiment. -/

def molecule : RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified "C12(OCCC1)OCCC2" [] with
  | .ok parsed => parsed.result.parsed.withExplicitHydrogens
  | .error _ => { atoms := [], bonds := [] }

theorem molecule_wellFormed : molecule.WellFormed := by
  unfold RawMolecule.WellFormed RawMolecule.BondEndpointsOK
  decide +kernel

/-- Exchange the rings and carry the corresponding explicit hydrogen atoms. -/
def exchange : Fin 21 → Fin 21 :=
  ![0,5,6,7,8,1,2,3,4,15,16,17,18,19,20,9,10,11,12,13,14]

theorem equivalent_pairs :
    molecule.atomCount = 21 ∧ exchange 0 = 0 ∧ exchange 1 = 5 ∧ exchange 4 = 8 ∧
    (∀ i, exchange (exchange i) = i ∧ molecule.atoms[(exchange i).val]? = molecule.atoms[i.val]?) ∧
    (∀ i j, molecule.bondOrder (exchange i) (exchange j) = molecule.bondOrder i j) := by
  decide +kernel

/-- Reverse the path so position one identifies the outgoing ligand occurrence. -/
def chosenBranches (mol : RawMolecule) (focus chosen : Nat) : List Nat :=
  (molecularPaths mol focus [chosen]).filterMap fun path => path.reverse[1]?

theorem chosenBranches_exact (mol : RawMolecule) (wf : mol.WellFormed)
    (focus chosen ligand : Nat) (valid : focus < mol.atomCount) :
    ligand ∈ chosenBranches mol focus chosen ↔ ∃ tail,
      RealPath (bondedAtoms mol) focus (chosen :: tail) ∧ chosen ≠ focus ∧
        (chosen :: tail).reverse[1]? = some ligand := by
  simp only [chosenBranches,List.mem_filterMap]
  constructor
  · rintro ⟨p,hp,h⟩
    cases p with
    | nil => simp at h
    | cons a tail =>
      obtain ⟨real,ne,mem⟩ := (molecularPaths_exact mol wf focus valid [chosen] a tail).mp hp
      have ac : a = chosen := by simpa using mem
      subst a
      exact ⟨tail,real,ne,h⟩
  · rintro ⟨tail,real,ne,h⟩
    exact ⟨_,(molecularPaths_exact mol wf focus valid [chosen] chosen tail).mpr
      ⟨real,ne,by simp⟩,h⟩

theorem oxygen_paths :
    (molecularPaths molecule 0 [1]).map List.reverse = [[0,1],[0,4,3,2,1]] ∧
    (molecularPaths molecule 0 [5]).map List.reverse = [[0,5],[0,8,7,6,5]] := by
  decide +kernel

def sourcePriority (chosen : Option Nat) (ligand : Nat) : Nat :=
  let z := (molecule.atoms[ligand]?.map fun a => a.element.atomicNumber).getD 0
  2*z + if chosen.any (fun o => (chosenBranches molecule 0 o).contains ligand) then 1 else 0

/-- Encodes a first-priority/ordinary stereogenic distinction in the signed
comparison convention of the public sorter. Equality is encoded by zero. -/
def sourceValue (chosen : Option Nat) (left right : Nat) : Int :=
  let a := sourcePriority chosen left
  let b := sourcePriority chosen right
  if a < b then -1 else if b < a then 1 else 0

theorem sourceValue_exact (o : Option Nat) (a b : Nat) :
    (sourceValue o a b = 0 ↔ sourcePriority o a = sourcePriority o b) ∧
    (sourceValue o a b = 1 ↔ sourcePriority o a > sourcePriority o b) ∧
    (sourceValue o a b = -1 ↔ sourcePriority o a < sourcePriority o b) ∧
    (sourceValue o a b).natAbs ≤ 1 := by
  rcases lt_trichotomy (sourcePriority o a) (sourcePriority o b) with h | h | h
  · simp [sourceValue,h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
  · simp [sourceValue,h]
  · simp [sourceValue,h,not_lt_of_ge (le_of_lt h),ne_of_gt h]

def sourceOrder (chosen : Nat) : List Nat :=
  replayListSort (fun a b => sourcePriority (some chosen) a ≥ sourcePriority (some chosen) b)
    (bondedAtoms molecule 0)

theorem oxygen_orders : sourceOrder 1 = [1,5,4,8] ∧ sourceOrder 5 = [5,1,8,4] := by
  decide +kernel

def sourceLetter (geometry : Geometry) (chosen : Nat) : Option LocalizedAuxiliaryLabel :=
  (readback? geometry (sourceOrder chosen)).map (.chiral ·)

/-- Reversing the initial oxygen choice exchanges both pairs. Their two
transpositions preserve the letter for every geometry, including missing points. -/
theorem choice_independent (g : Geometry) : sourceLetter g 1 = sourceLetter g 5 := by
  simp only [sourceLetter,oxygen_orders.1,oxygen_orders.2]
  rw [LocalizedMarkedTerminalGaugeSwap.readback_swap34 g 5 1 4 8,
      LocalizedMarkedTerminalGaugeSwap.readback_swap12 g 1 5 4 8]
  cases readback? g [1,5,4,8] with
  | none => rfl
  | some r => cases r <;> rfl

def comparisonsMatch (chosen : Option Nat) (cs : List Comparison) : Bool :=
  cs.all fun c => (bondedAtoms molecule 0).contains c.left &&
    (bondedAtoms molecule 0).contains c.right && c.value == sourceValue chosen c.left c.right

theorem matches_exact (chosen : Option Nat) (cs : List Comparison) :
    comparisonsMatch chosen cs = true ↔ ∀ c ∈ cs, c.left ∈ bondedAtoms molecule 0 ∧
      c.right ∈ bondedAtoms molecule 0 ∧ c.value = sourceValue chosen c.left c.right := by
  simp [comparisonsMatch, and_assoc]

/-- All comparison sites in the annotated example, including the additional
adjacent comparisons used to discover classes. Each pass carries its own mark. -/
def checkComparisons (t : CenterTrace) : Option Nat := do
  guard (t.atom == 0 && t.discovered.isEmpty && t.updates.isEmpty)
  let [first,full] := t.passes | none
  let [constitution] := first.trials | none
  let [base,promoted] := full.trials | none
  let some o := promoted.mark | none
  guard ((o == 1 || o == 5) && constitution.mark.isNone && base.mark.isNone &&
    first.after.isNone && full.after.isNone && first.groups.isEmpty)
  guard (comparisonsMatch none constitution.comparisons && comparisonsMatch none base.comparisons &&
    comparisonsMatch none full.groups && comparisonsMatch (some o) promoted.comparisons)
  return o

structure Checked (input : LocalizedChemicalRing.Input) where
  replay : Result input [0]
  trace : CenterTrace
  choice : Nat
  molecule_eq : input.molecule = molecule
  traces_eq : replay.traces = [trace]
  comparisons_eq : checkComparisons trace = some choice
  report_eq : replay.report = [(0,sourceLetter (inputGeometry input.certified) choice)]

/-- Offline source comparison and public replay on the same molecular input. -/
def check (input : LocalizedChemicalRing.Input) (packet : Receipt) : Except String (Checked input) := do
  if hm : input.molecule = molecule then
    let r ← checkReceipt input packet [0]
    match ht : r.traces with
    | [t] =>
      match hc : checkComparisons t with
      | some o =>
        if hr : r.report = [(0,sourceLetter (inputGeometry input.certified) o)] then
          return ⟨r,t,o,hm,ht,hc,hr⟩
        else throw "spiro source reading differs"
      | none => throw "spiro molecular comparison differs"
    | _ => throw "expected the annotated spiro center"
  else throw "expected the published dioxaspiro molecule"

end TetraStereo.Engine.CentresRing.SpiroSource
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.equivalent_pairs
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.chosenBranches_exact
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.oxygen_paths
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.sourceValue_exact
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.oxygen_orders
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.matches_exact
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.check
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.choice_independent
assert_kernel_only TetraStereo.Engine.CentresRing.SpiroSource.molecule_wellFormed
