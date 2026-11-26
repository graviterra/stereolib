import TetraStereo.Engine.RingSecondShellIncidence

/-! Two graph observations common to every actual ligand direction. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAllLigandTwoShell
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRetainedChemicalTrace (Word Key)
open RingRetainedChemicalPreorder (Site Direction keyFor read_key orderWord)
open RingAtomicNeighborOrder (record written)
open private sourceNode from TetraStereo.Engine.RingRetainedChemicalCoverage
attribute [local instance] lexOrd

def siteAtom (i : Input) (f : Site i) := f.val.node.current?.getD f.val.root

theorem site_current (i : Input) (f : Site i) : f.val.node.current? = some (siteAtom i f) := by
  obtain ⟨a,atAtom,_⟩ := sourceNode i (i.certified.carrierOccurrence_legitimate i.single f)
  simp [siteAtom,atAtom]

/-- The incoming edge is removed from a real endpoint. A terminal closure carries
the atomic number of the represented atom and an empty second row. -/
noncomputable def physical (i : Input) (f : Site i) (a : Direction i f) : Word :=
  [[(record i (siteAtom i a.val)).element.atomicNumber],
    RingSecondShellIncidence.secondWord i ⟨a.val,some f⟩ (siteAtom i f) (siteAtom i a.val)]

theorem atomic_decomposition {i : Input} {f : Site i} (a : Direction i f) :
    (keyFor a).atomic.word = physical i f a ++ (keyFor a).atomic.word.drop 2 := by
  have h := ((RingRetainedChemicalTrace.key_source (read_key a)).formed .atomic).2
  change (keyFor a).atomic.word = [(keyFor a).root.atomic] :: (keyFor a).atomic.levels.flatten at h
  have atZ := RingPyramidalConstitution.key_atomic (site_current i a.val)
    (written i (siteAtom i a.val)) (read_key a)
  have neighbor := (i.certified.mem_localizedRerootNeighborFrames_iff f.val a.val.val).mpr
    ⟨a.val.property,a.property⟩
  have row := RingSecondShellIncidence.all_second_row i i.single ⟨a.val,some f⟩ f rfl
    (i.certified.mem_localizedRerootNeighborFrames_symm f _ neighbor) _ _
    (site_current i a.val) (site_current i f) (read_key a)
  rw [h] at row ⊢
  rw [atZ]
  cases rest : (keyFor a).atomic.levels.flatten with
  | nil => simp [rest] at row
  | cons x xs =>
    have hx : x = _ := Option.some.inj (by simpa [rest] using row)
    simp [physical,hx]

def remaining (k : Key) : List Word := [k.atomic.word.drop 2,k.duplicate.word,k.mass.word]

private theorem split_compare (x y u v : List Nat) (ta tb : Word) (la lb : List Word) :
    compare ((x :: u :: ta) :: la) ((y :: v :: tb) :: lb) =
      (compare [x,u] [y,v]).then (compare (ta :: la) (tb :: lb)) := by
  simp only [List.compare_cons_cons]
  cases compare x y <;> cases compare u v <;> rfl

/-- A strict two-shell decision fixes the complete constitutional order. A tie
continues with every remaining atomic row, followed by duplicate and mass rows. -/
theorem compare_factor {i : Input} {f : Site i} (a b : Direction i f) :
    compare (orderWord (keyFor a)) (orderWord (keyFor b)) =
      (compare (physical i f a) (physical i f b)).then
        (compare (remaining (keyFor a)) (remaining (keyFor b))) := by
  unfold orderWord
  conv_lhs => rw [atomic_decomposition a,atomic_decomposition b]
  exact split_compare ..

private theorem word_lt (a b : Word) : compare a b = .lt ↔ a < b := by
  exact DeclarativeCIP.compareLex_eq_lt_iff_of compare
    (DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
      (fun _ _ => Std.compare_eq_eq_iff_eq)) (fun _ _ => Std.compare_eq_eq_iff_eq) a b

theorem word_lt_of_prefix {i : Input} {f : Site i} (a b : Direction i f)
    (lt : physical i f a < physical i f b) : orderWord (keyFor a) < orderWord (keyFor b) := by
  apply (RingFullPathConstitution.word_lt ..).mp
  rw [compare_factor,(word_lt ..).mpr lt]
  rfl

theorem table_exact {i : Input} {f : Site i} (a b : Direction i f) :
    RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i f) a b =
      some ((compare (physical i f a) (physical i f b)).then
        (compare (remaining (keyFor a)) (remaining (keyFor b)))) := by
  rw [RingRetainedChemicalPreorder.table_order,compare_factor]

/-- Remove just the two independently reconstructed rows inside the first trial field. -/
def remainingTrial : List (List Word) → List (List Word)
  | (atomic :: rest) :: stages => (atomic.drop 2 :: rest) :: stages
  | stages => stages

private theorem through_direction {i : Input} {f : Site i} (a : Direction i f)
    {r : RingNestedActivePair.Reader i} {rev} {k : RingFullPathEligibility.Key}
    (read : RingFullPathEligibility.Reads i r rev ⟨a.val,some f⟩ k) :
    ∃ u : Word, k.throughFourA = orderWord (keyFor a) ++ [u] := by
  obtain ⟨u,_,_,_,_,du,_,_,_,_,rfl⟩ := read
  have unitRead : RingRetainedUnitPass.Reading i r rev ⟨a.val,some f⟩ u := du
  obtain ⟨c,hc,prior⟩ := unitRead.constitution
  have same := Option.some.inj (hc.symm.trans (read_key a))
  exact ⟨u.word,congrArg (fun words => words ++ [u.word]) (prior.trans (congrArg orderWord same))⟩

private theorem split_trial (x y u v : List Nat) (ta tb : Word) (la lb : List Word)
    (pa pb : List (List Word)) :
    compare (((x :: u :: ta) :: la) :: pa) (((y :: v :: tb) :: lb) :: pb) =
      (compare [x,u] [y,v]).then (compare ((ta :: la) :: pa) ((tb :: lb) :: pb)) := by
  simp only [List.compare_cons_cons]
  cases compare x y <;> cases compare u v <;> rfl

/-- Every completed reading on either geometry factors through the graph prefix,
including arbitrary promotion marks. In a two-shell tie the remaining comparison
retains the rest of Rule 1a as well as all subsequent rules. -/
theorem trial_factor {i : Input} {f : Site i} (a b : Direction i f)
    {r : RingNestedActivePair.Reader i} {rev} {x y : RingFullPathEligibility.Key}
    (rx : RingFullPathEligibility.Reads i r rev ⟨a.val,some f⟩ x)
    (ry : RingFullPathEligibility.Reads i r rev ⟨b.val,some f⟩ y)
    (ma mb : Word) :
    compare (RingFullPathTrialReadings.trialKey x ma) (RingFullPathTrialReadings.trialKey y mb) =
      (compare (physical i f a) (physical i f b)).then
        (compare (remainingTrial (RingFullPathTrialReadings.trialKey x ma))
          (remainingTrial (RingFullPathTrialReadings.trialKey y mb))) := by
  obtain ⟨u,hx⟩ := through_direction a rx
  obtain ⟨v,hy⟩ := through_direction b ry
  simp only [RingFullPathTrialReadings.trialKey,hx,hy,orderWord,List.cons_append,List.nil_append,remainingTrial]
  conv_lhs => rw [atomic_decomposition a,atomic_decomposition b]
  exact split_trial ..

end TetraStereo.Engine.RingAllLigandTwoShell
assert_kernel_only TetraStereo.Engine.RingAllLigandTwoShell.atomic_decomposition
assert_kernel_only TetraStereo.Engine.RingAllLigandTwoShell.compare_factor
assert_kernel_only TetraStereo.Engine.RingAllLigandTwoShell.table_exact
assert_kernel_only TetraStereo.Engine.RingAllLigandTwoShell.trial_factor
