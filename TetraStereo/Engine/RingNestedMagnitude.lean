import TetraStereo.Engine.RingRetainedChemicalPreorder
import TetraStereo.Engine.RingNestedActivePair
import TetraStereo.Engine.RingJointObservations
import TetraStereo.Engine.RingActiveMagnitude
import TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingNestedActivePair
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingActivePairs (swapWalk molecularValues)
open RingActivePairReport (Score Slot changes reversals doubled)
open RingSeededPairs (localSign? listSign?)
open CentresRing.PairList (combine)

private theorem projections (v : Visit) (h : v.publication.all consistent = true) :
    unit (v.label true) = unit (v.label false) ∧
    lower (v.label true) = lower (v.label false) ∧
    upper (v.label true) = (upper (v.label false)).map RS.swap := by
  rcases v with ⟨addr,z,n,_ | ⟨a,b⟩⟩
  · exact ⟨rfl,rfl,rfl⟩
  · cases a with
    | chiral x =>
      cases b with
      | chiral y => cases x <;> cases y <;> first | exact ⟨rfl,rfl,rfl⟩ | contradiction
      | pseudoasymmetric y => contradiction
    | pseudoasymmetric x =>
      cases b with
      | chiral y => contradiction
      | pseudoasymmetric y => cases x <;> cases y <;> first | exact ⟨rfl,rfl,rfl⟩ | contradiction

private theorem sources_physical {i read qs data}
    (sources : List.Forall₂ (NodeSource i read) qs data) :
    ∀ d ∈ data, d.1.publication.all consistent = true := by
  induction sources with
  | nil => simp
  | cons h t ih => simpa only [List.forall_mem_cons] using And.intro h.physical ih

private theorem walk_physical {i read qs xs} (walk : Walk i read qs xs) :
    ∀ v ∈ xs.flatten, v.publication.all consistent = true := by
  induction walk with
  | empty => simp
  | layer visits _ ih =>
    intro v hv
    rcases List.mem_append.mp hv with head | tail
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp head
      exact sources_physical visits d hd
    · exact ih v tail

private theorem descriptors_mem {xs : List (List Visit)} {v} (h : v ∈ descriptors xs) :
    v ∈ xs.flatten := by
  cases xs with
  | nil => contradiction
  | cons top tail =>
    rcases List.mem_append.mp h with head | rest
    · exact List.mem_append_left _ head
    · obtain ⟨layer,hl,hv⟩ := List.mem_flatMap.mp rest
      exact List.mem_append_right _ (List.mem_flatten_of_mem hl (List.mem_filter.mp hv).1)

private def upperWord (xs : List (List Visit)) (rev : Bool) :=
  (descriptors xs).map fun v => upper (v.label rev)

private def lowerWord (xs : List (List Visit)) (rev : Bool) :=
  xs.flatten.map fun v => lower (v.label rev)

private theorem physical_words {xs : List (List Visit)}
    (all : ∀ v ∈ xs.flatten, v.publication.all consistent = true) :
    unitWord xs true = unitWord xs false ∧ lowerWord xs true = lowerWord xs false ∧
    upperWord xs true = swapWalk (upperWord xs false) := by
  refine ⟨congrArg List.flatten (List.map_congr_left ?_), List.map_congr_left ?_, ?_⟩
  · intro layer hl
    exact List.map_congr_left fun v hv => (projections v (all v (List.mem_flatten_of_mem hl hv))).1
  · exact fun v hv => (projections v (all v hv)).2.1
  · unfold upperWord swapWalk
    rw [List.map_map]
    exact List.map_congr_left fun v hv => (projections v (all v (descriptors_mem hv))).2.2

private theorem lower_range (a b : List Nat) : lowerScore a b ∈ ([-1,0,1] : List Int) := by
  induction a generalizing b with
  | nil => cases b <;> simp [lowerScore]
  | cons x xs ih =>
    cases b with
    | nil => simp [lowerScore]
    | cons y ys =>
      by_cases e : x = y
      · simpa only [lowerScore,if_pos e] using ih ys
      · by_cases lt : y < x <;> simp [lowerScore,e,lt]

private def evaluate (a c : Int) (x y : List (Option RS)) : Option Int := do
  if a ≠ 0 then return a
  let b ← localSign? x y
  if b ≠ 0 then return b
  if c ≠ 0 then return c
  let r ← listSign? .R x y
  let s ← listSign? .S x y
  return combine r s

private theorem stable_sign {z h k : Int} (range : z ∈ ([-1,0,1] : List Int))
    (a : some z = some h) (b : some z = some k) : (h,k) ∈ molecularValues := by
  obtain rfl := Option.some.inj a
  obtain rfl := Option.some.inj b
  simp only [List.mem_cons,List.not_mem_nil,or_false] at range
  rcases range with rfl | rfl | rfl <;> decide

private theorem evaluate_scores (a c : Int) (x y : List (Option RS)) {h k : Int}
    (ra : a ∈ ([-1,0,1] : List Int)) (rc : c ∈ ([-1,0,1] : List Int))
    (actual : evaluate a c x y = some h) (reflected : evaluate a c (swapWalk x) (swapWalk y) = some k) :
    (h,k) ∈ molecularValues := by
  by_cases az : a = 0
  · subst a
    cases loc : localSign? x y with
    | none => simp [evaluate,loc] at actual
    | some b =>
      have other := (RingActivePairs.local_swap x y).trans loc
      by_cases bz : b = 0
      · subst b
        by_cases cz : c = 0
        · subst c
          cases r : listSign? .R x y with
          | none => simp [evaluate,loc,r] at actual
          | some v =>
            have s : listSign? .S x y = some (-v) := by simp [RingSeededPairs.two_seed_sign,r]
            have rr := (RingActivePairs.fixed_swap .R x y).trans s
            have rs := (RingActivePairs.fixed_swap .S x y).trans r
            have hh : combine v (-v) = h := by simpa [evaluate,loc,r,s] using actual
            have kk : combine (-v) v = k := by simpa [evaluate,other,rr,rs] using reflected
            rw [← hh,← kk]
            have rv := RingActivePairs.seed_range r
            simp only [List.mem_cons,List.not_mem_nil,or_false] at rv
            rcases rv with rfl | rfl | rfl <;> decide
        · exact stable_sign rc (by simpa [evaluate,loc,cz] using actual)
            (by simpa [evaluate,other,cz] using reflected)
      · exact stable_sign (RingActivePairs.local_range loc) (by simpa [evaluate,loc,bz] using actual)
          (by simpa [evaluate,other,bz] using reflected)
  · exact stable_sign ra (by simpa [evaluate,az] using actual) (by simpa [evaluate,az] using reflected)

/-- Evaluate the signed stages on one complete enumeration of the frozen
observations after constitution has tied. The independence of this
enumeration is a separate condition for an unordered molecular profile. -/
def projectedScore? (xs ys : List (List Visit)) (rev : Bool) :=
  evaluate (lowerScore (unitWord xs rev) (unitWord ys rev))
    (lowerScore (lowerWord xs rev) (lowerWord ys rev)) (upperWord xs rev) (upperWord ys rev)

/-- Mirror consistency alone restricts the signed values to the five molecular
pairs, even when a preceding rule permits several different visit orders. -/
theorem projected_score_pair {xs ys : List (List Visit)} {h k : Int}
    (left : ∀ v ∈ xs.flatten, v.publication.all consistent = true)
    (right : ∀ v ∈ ys.flatten, v.publication.all consistent = true)
    (original : projectedScore? xs ys false = some h)
    (reflected : projectedScore? xs ys true = some k) : (h,k) ∈ molecularValues := by
  obtain ⟨lu,ll,lh⟩ := physical_words left
  obtain ⟨ru,rl,rh⟩ := physical_words right
  unfold projectedScore? at reflected
  rw [lu,ru,ll,rl,lh,rh] at reflected
  exact evaluate_scores _ _ _ _ (lower_range ..) (lower_range ..) original reflected

private theorem decide_eq {xs ys : List (List Visit)} (rev : Bool)
    (top : xs.map (List.map topology) = ys.map (List.map topology)) :
    decide? xs ys rev = evaluate (lowerScore (unitWord xs rev) (unitWord ys rev))
      (lowerScore (lowerWord xs rev) (lowerWord ys rev)) (upperWord xs rev) (upperWord ys rev) := by
  simp [decide?,top,evaluate,lowerWord,upperWord]

/-- The source walks of an accepted comparison enforce fixed unit and lowercase readings
and reversed uppercase hands. This constrains both scores, including their magnitudes. -/
theorem Pair.signed_scores {i f a b read} (p : Pair i f a b read) : p.scores ∈ molecularValues := by
  obtain ⟨left,right⟩ := p.source_walks
  obtain ⟨lu,ll,lh⟩ := physical_words (walk_physical left)
  obtain ⟨ru,rl,rh⟩ := physical_words (walk_physical right)
  have actual := p.actual
  have reflected := p.reflected
  by_cases top : p.left.map (List.map topology) = p.right.map (List.map topology)
  · rw [decide_eq false top] at actual
    rw [decide_eq true top,lu,ru,ll,rl,lh,rh] at reflected
    exact evaluate_scores _ _ _ _ (lower_range ..) (lower_range ..) actual reflected
  · simp [decide?,top] at actual

theorem Edge.signed_scores {i f a b read s} (e : Edge i f a b read s) : s ∈ molecularValues := by
  cases e with
  | below => decide
  | above => decide
  | stereo p => exact p.signed_scores

/-- Each of the six ranked molecular directions reverses precisely at magnitude two. -/
theorem Assignment.reversals_eq_doubled {i f read} (o : Assignment i f read) :
    reversals o.matrix = doubled o.matrix := by
  apply (List.Perm.refl _).countP_congr
  intro p mem
  have ne := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem)
  have h := (o.edge p.1 p.2 ne).signed_scores
  let score := o.matrix.get p.1 p.2
  change score ∈ molecularValues at h
  change (decide (0 < score.1) != decide (0 < score.2)) = (score.1.natAbs == 2)
  simp only [molecularValues,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

private def Frame.atom {i f} (fr : Frame i f) (k : Slot) : Nat :=
  fr.ids.get (Fin.cast (by simpa [RingRetainedAuxiliary.canonical] using fr.physical.length_eq.symm) k)

/-- The direction at a retained ranking slot is its actual adjacent molecular occurrence. -/
def Frame.direction {i f} (fr : Frame i f) (k : Slot) : RingRetainedChemicalPreorder.Direction i f :=
  ⟨(fr.arm k).occurrence,by
    let cursor : RingActivePairs.Arm i := ⟨f,none⟩
    have present : fr.arm k ∈ i.certified.executableLocalizedRerootChildren cursor := List.get_mem ..
    have intended := i.certified.executableLocalizedRerootChildren_map cursor
    have belongs := List.mem_map_of_mem (f := fun (c : RingActivePairs.Arm i) => c.occurrence.val) present
    rw [intended] at belongs
    exact ((i.certified.mem_localizedRerootNeighborFrames_iff f.val _).mp
      (i.certified.mem_localizedRerootNeighborFrames_of_mem_intended cursor _ belongs)).2⟩

/-- Distinct ranking slots have distinct addresses, since equal addresses at the same
original root give the same occurrence and hence the same physical ligand atom. -/
theorem Frame.incident {i f} (fr : Frame i f) {a b : Slot} (different : a ≠ b) :
    RingRetainedConstitution.Incident i.certified f (fr.direction a).val (fr.direction b).val := by
  have real := ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).1
  refine ⟨by simp [OfficialCIPNode.isDuplicateLeaf,real,OfficialCIPNodeProvenance.isDuplicateLeaf],?_,
    (fr.direction a).property,(fr.direction b).property⟩
  intro address
  have same := i.certified.declarativeLocalizedOccurrence_functional_at_root_address
    ((i.certified.mem_localizedOccurrences_iff _ _).mp (fr.direction a).val.property)
    ((i.certified.mem_localizedOccurrences_iff _ _).mp (fr.direction b).val.property)
    ((fr.direction a).property.1.trans (fr.direction b).property.1.symm) address
  have ident := congrArg (fun x : i.certified.LocalizedCIPOccurrenceFrame => x.node.current?.map Fin.val) same
  change (fr.arm a).occurrence.val.node.current?.map Fin.val =
    (fr.arm b).occurrence.val.node.current?.map Fin.val at ident
  rw [fr.point_at a,fr.point_at b] at ident
  have unique : (RingRetainedAuxiliary.canonical i.certified fr.center).Nodup :=
    List.Nodup.map (Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective fr.center))
      (List.nodup_finRange 4)
  have ids := fr.physical.nodup_iff.mpr unique
  have numbered := ids.get_inj_iff.mp (show fr.atom a = fr.atom b from Option.some.inj ident)
  have eqNat := congrArg (fun j : Fin fr.ids.length => j.val) numbered
  exact different (Fin.ext eqNat)

/-- The five exhaustive constitutional multiplicity shapes applied to all four
physical directions of this exact retained frame. -/
theorem Frame.five_shapes {i f} (fr : Frame i f) :
    RingRetainedChemicalPreorder.blockSizes (RingRetainedChemicalPreorder.representative fr.direction) ∈
      ([[1,1,1,1],[1,1,2],[2,2],[1,3],[4]] : List (List Nat)) :=
  RingRetainedChemicalPreorder.five_shapes fr.direction

private theorem Frame.reordered {i f} (fr : Frame i f) (g : Geometry) (o : RingJointObservations.Order) :
    readback? g (fr.atoms o.val) =
      if RingJointObservations.parity o then readback? g [fr.atom 0,fr.atom 1,fr.atom 2,fr.atom 3]
      else (readback? g [fr.atom 0,fr.atom 1,fr.atom 2,fr.atom 3]).map RS.swap := by
  have lookup (k : Slot) : [fr.atom 0,fr.atom 1,fr.atom 2,fr.atom 3][k.val]? = some (fr.atom k) := by
    fin_cases k <;> rfl
  have select (xs : List Slot) : atomsAt? [fr.atom 0,fr.atom 1,fr.atom 2,fr.atom 3] (xs.map Fin.val) =
      some (fr.atoms xs) := by
    change _ = some (xs.map fr.atom)
    induction xs with
    | nil => rfl
    | cons k xs ih =>
      unfold atomsAt? at ih ⊢
      simp only [List.map_cons,List.mapM_cons,lookup,ih]
      rfl
  have law := LocalizedMarkedConfigurationTransport.reordered_readback_partial g fr.atom (o.val.map Fin.val)
    (show (o.val.map Fin.val).Perm [0,1,2,3] from o.property.map Fin.val)
  rw [select] at law
  exact law

/-- Physical reads of any two rankings on this retained frame determine the absolute
hand and the casing from the parity of its reversing edges, for every scoring reader. -/
theorem Frame.label_by_reversals {i f} (fr : Frame i f) {reader : RingActivePairReport.Reader}
    {mat : RingActivePairReport.Matrix reader} (rank : RingActivePairReport.Ranking mat false)
    (mirrorRank : RingActivePairReport.Ranking mat true) {hand mirrorHand : RS}
    (physical : readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms rank.slots) = some hand)
    (mirrorPhysical : readback? (mirror (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified))
      (fr.atoms mirrorRank.slots) = some mirrorHand) :
    label hand mirrorHand = if reversals mat % 2 = 0 then .chiral hand else .pseudoasymmetric (pseudoRSOfRS hand) := by
  let actual : RingJointObservations.Order := ⟨rank.slots,rank.perm⟩
  let reflected : RingJointObservations.Order := ⟨mirrorRank.slots,mirrorRank.perm⟩
  let g := LocalizedChemicalRingPhysicalSense.inputGeometry i.certified
  have first := (fr.reordered g actual).symm.trans physical
  have other := mirrorPhysical
  change readback? (mirror g) (fr.atoms reflected.val) = some mirrorHand at other
  rw [readback_mirror,fr.reordered g reflected] at other
  have eqn := RingJointObservations.same_parity actual reflected
  change RingJointObservations.parity actual = RingJointObservations.parity reflected ↔
    changes rank.slots mirrorRank.slots % 2 = 0 at eqn
  rw [RingActivePairReport.changes_eq rank mirrorRank] at eqn
  cases ha : RingJointObservations.parity actual <;> cases hb : RingJointObservations.parity reflected <;>
    cases base : readback? g [fr.atom 0,fr.atom 1,fr.atom 2,fr.atom 3] with
    | none => simp [ha,base] at first
    | some s =>
      cases s <;> cases h : hand <;> cases m : mirrorHand <;> simp_all [label,RS.swap]

/-- An assigned retained occurrence has the absolute hand of its actual geometric reading.
Its case is fixed by the parity of its six comparisons of doubled magnitude. The successful
coordinate reads already present in the assignment suffice, even with partial geometry. -/
theorem Assignment.casing_by_magnitude {i f read} (o : Assignment i f read) :
    o.labels.1 = if doubled o.matrix % 2 = 0 then .chiral o.hand else .pseudoasymmetric (pseudoRSOfRS o.hand) := by
  rw [← o.reversals_eq_doubled]
  exact o.frame.label_by_reversals o.actual o.reflected o.physical o.mirrorPhysical

theorem Assignment.lower_iff_odd {i f read} (o : Assignment i f read) :
    RingJointObservations.isLower (some o.labels.1) = true ↔ doubled o.matrix % 2 = 1 := by
  rw [o.casing_by_magnitude]
  split <;> simp_all [RingJointObservations.isLower]

/-- At the public occurrence publisher a lowercase label is equivalent to an issued
masked assignment with an odd count of doubled molecular comparisons. -/
theorem publication_lower_iff {i f read v} (hit : publish? i f read = some (some v)) :
    RingJointObservations.isLower (some v.1) = true ↔
      ∃ a : Assignment i f (masked f read), assign? i f (masked f read) = some a ∧
        v = a.labels ∧ doubled a.matrix % 2 = 1 := by
  constructor
  · intro low
    rcases publication_source hit with ⟨h,_,rfl⟩ | ⟨a,issued,rfl⟩
    · contradiction
    · exact ⟨a,issued,rfl,a.lower_iff_odd.mp low⟩
  · rintro ⟨a,_,rfl,odd⟩
    exact a.lower_iff_odd.mpr odd

end TetraStereo.Engine.RingNestedActivePair

assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Edge.signed_scores
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Assignment.reversals_eq_doubled
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Assignment.casing_by_magnitude
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Assignment.lower_iff_odd
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.publication_lower_iff
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Frame.incident
assert_kernel_only TetraStereo.Engine.RingNestedActivePair.Frame.five_shapes

assert_kernel_only TetraStereo.Engine.RingNestedActivePair.projected_score_pair
