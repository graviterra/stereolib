import TetraStereo.Engine.RingSingleDonorComparison

/-! Native comparisons between ligand arms whose uppercase donors are exchanged
pointwise. Lowercase labels and the unsigned molecular carrier are retained. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOppositeDonorArms
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels)
open RingGeometryExchange (Carrier Frozen)
open RingSplitLigandTie (markingReader)
open RingFullPathPairs (likeAt handAt stage)
open RingFullPathEligibility (Key Reads)
open RingSingleDonorComparison (donors onGeometry)
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

/-- Exchange uppercase hands throughout both columns while retaining lowercase observations. -/
def conjugate : LocalizedTetrahedralRSPseudoDescriptor → LocalizedTetrahedralRSPseudoDescriptor
  | .chiral h => .chiral h.swap
  | .pseudoasymmetric h => .pseudoasymmetric h

def flip (v : Labels) : Labels := (conjugate v.1,conjugate v.2)

/-- The full frozen publication at every matched cursor, including absence. -/
def Opposite {i j : Input} (c : Carrier i j) (l : Reader i) (r : Reader j) :=
  ∀ q, c.domain q → r (c.image q).occurrence = (l q.occurrence).map (Option.map flip)

private theorem norm (v : Option Labels) (consistent : v.all RingNestedActivePair.consistent = true) :
    (v.map flip).map RingSplitLigandTie.normalize = v.map RingSplitLigandTie.normalize := by
  rcases v with _ | ⟨(_|_),(_|_)⟩ <;> first | rfl | contradiction

/-- Only the native consistent cells on the correspondence are needed for unsigned transport. -/
private theorem unsigned {i j : Input} {l : Reader i} {r : Reader j} {c : Carrier i j}
    (op : Opposite c l r)
    (ok : ∀ q, c.domain q → ∀ v, l q.occurrence = some v → v.all RingNestedActivePair.consistent = true) :
    Frozen c (markingReader l) (markingReader r) := by
  intro q on
  unfold markingReader
  rw [op q on]
  cases h : l q.occurrence with
  | none => rfl
  | some v => exact congrArg some (norm v (ok q on v h)).symm

private theorem likes {i j : Input} {l : Reader i} {r : Reader j} {c : Carrier i j}
    (op : Opposite c l r) (rev : Bool) (seed : RS) (q : Arm i) (on : c.domain q) :
    likeAt j r rev seed.swap (c.image q) = likeAt i l rev seed q := by
  unfold likeAt handAt
  rw [op q on]
  rcases l q.occurrence with _ | (_ | ⟨a,b⟩) <;> cases rev <;> cases seed <;>
    first | rfl | (cases a with | chiral h => cases h <;> rfl | pseudoasymmetric h => rfl) |
      (cases b with | chiral h => cases h <;> rfl | pseudoasymmetric h => rfl)

private theorem transport {i j : Input} {l : Reader i} {r : Reader j} {c : Carrier i j}
    (op : Opposite c l r) (same : Frozen c (markingReader l) (markingReader r))
    (rev lower : Bool) (seed : RS) {q : Arm i} (on : c.domain q) {x y : List Bool}
    (a : (stage i l rev (if lower then [.lowercase] else [])).Source (likeAt i l rev seed) q x)
    (b : (stage j r rev (if lower then [.lowercase] else [])).Source (likeAt j r rev seed.swap) (c.image q) y) :
    x = y := by
  refine RingFullPathKeyTransport.source_transport _ _ _ _ c.image c.domain c.below c.children
    ?_ (likes op rev seed) on a b
  intro t ht u v hu hv
  cases lower
  · exact c.unit same ht (normalized_unit hu) (normalized_unit hv)
  · exact c.refinement same [.lowercase] t ht u v (normalized_lower hu) (normalized_lower hv)

/-- Unsigned and preferred-reference fields agree, even with an arbitrary mixture of
hands at one distance. The fixed R and S readings at both stages exchange. -/
private theorem wordsOn {i j : Input} {l : Reader i} {r : Reader j} {c : Carrier i j}
    (op : Opposite c l r)
    (ok : ∀ q, c.domain q → ∀ v, l q.occurrence = some v → v.all RingNestedActivePair.consistent = true)
    {f : Site i} {g : Site j} (rd : RingGroupedStereo.Ready f l) (rd' : RingGroupedStereo.Ready g r)
    (q : Arm i) (dom : c.domain q) (vq : i.certified.LocalizedRerootCursorValid q)
    (vp : j.certified.LocalizedRerootCursorValid (c.image q)) (oq : q.occurrence.val.root = f.val.root)
    (op' : (c.image q).occurrence.val.root = g.val.root) (rev : Bool) :
    ∃ a b : Key, RingFullPathEligibility.key? i l rev q = some a ∧
      RingFullPathEligibility.key? j r rev (c.image q) = some b ∧
      a.throughFourA = b.throughFourA ∧ a.bestFourB = b.bestFourB ∧ a.fourC = b.fourC ∧
      ∀ (lower : Bool) (seed : RS),
        RingFullPathPairs.stageWords i l rev (if lower then [.lowercase] else []) seed q =
        RingFullPathPairs.stageWords j r rev (if lower then [.lowercase] else []) seed.swap (c.image q) := by
  have same := unsigned op ok
  obtain ⟨a,ha,ea⟩ := RingFullPathEligibility.key_exact rd rev q vq oq
  obtain ⟨b,hb,eb⟩ := RingFullPathEligibility.key_exact rd' rev (c.image q) vp op'
  have eqword (lower : Bool) (seed : RS) :
      RingFullPathPairs.stageWords i l rev (if lower then [.lowercase] else []) seed q =
      RingFullPathPairs.stageWords j r rev (if lower then [.lowercase] else []) seed.swap (c.image q) := by
    let os : List RingRetainedStereoRefinement.Observation := if lower then [.lowercase] else []
    obtain ⟨x,hx,ex⟩ := (stage i l rev os).source_exact (likeAt i l rev seed)
      (RingOccurrenceStereo.rank_total rd rev os) q vq oq
    obtain ⟨y,hy,ey⟩ := (stage j r rev os).source_exact (likeAt j r rev seed.swap)
      (RingOccurrenceStereo.rank_total rd' rev os) (c.image q) vp op'
    exact hx.trans ((congrArg some (transport op same rev lower seed dom ((ex _).mpr rfl) ((ey _).mpr rfl))).trans hy.symm)
  obtain ⟨_,_,_,_,_,ua,la,ar,as',_,rfl⟩ := (ea a).mpr rfl
  obtain ⟨_,_,_,_,_,ub,lb,br,bs,_,rfl⟩ := (eb b).mpr rfl
  have un := c.unit same dom (normalized_unit ua) (normalized_unit ub)
  have lo := c.refinement same [.lowercase] q dom _ _ (normalized_lower la) (normalized_lower lb)
  have rs := transport op same rev false .R dom ar bs
  have sr := transport op same rev false .S dom as' br
  exact ⟨_,_,ha,hb,congrArg RingStereoSiblingPass.Branch.deep un,by
    dsimp; rw [rs,sr,max_comm],congrArg RingStereoSiblingPass.Branch.word lo,eqword⟩

/-- Unsigned and preferred-reference fields agree, even with an arbitrary mixture of
hands at one distance. The fixed R and S readings at both stages exchange. -/
theorem words {i j : Input} {l : Reader i} {r : Reader j} {c : Carrier i j}
    (op : Opposite c l r)
    {f : Site i} {g : Site j} (rd : RingGroupedStereo.Ready f l) (rd' : RingGroupedStereo.Ready g r)
    (q : Arm i) (dom : c.domain q) (vq : i.certified.LocalizedRerootCursorValid q)
    (vp : j.certified.LocalizedRerootCursorValid (c.image q)) (oq : q.occurrence.val.root = f.val.root)
    (op' : (c.image q).occurrence.val.root = g.val.root) (rev : Bool) :
    ∃ a b : Key, RingFullPathEligibility.key? i l rev q = some a ∧
      RingFullPathEligibility.key? j r rev (c.image q) = some b ∧
      a.throughFourA = b.throughFourA ∧ a.bestFourB = b.bestFourB ∧ a.fourC = b.fourC ∧
      ∀ (lower : Bool) (seed : RS),
        RingFullPathPairs.stageWords i l rev (if lower then [.lowercase] else []) seed q =
        RingFullPathPairs.stageWords j r rev (if lower then [.lowercase] else []) seed.swap (c.image q) := by
  let sub : Carrier i j := {
    image := c.image
    domain := fun p => c.domain p ∧ p.occurrence.val.root = f.val.root
    below := fun p hp t ht => ⟨c.below p hp.1 t ht,
      (i.certified.localizedRerootChildren_root_eq p t _
        (i.certified.executableLocalizedRerootChildren_declarative p) ht).trans hp.2⟩
    children := fun p hp => c.children p hp.1
    observation := fun p hp => c.observation p hp.1 }
  have matched : Opposite sub l r := fun p hp => op p hp.1
  apply wordsOn matched _ rd rd' q ⟨dom,oq⟩ vq vp oq op' rev
  intro p hp v seen
  obtain ⟨w,hw,valid,_⟩ := rd p hp.2
  exact Option.some.inj (hw.symm.trans seen) ▸ valid

private theorem count_likes (ds : List RS) (rev : Bool) (s : RS) :
    ((ds.map (fun h => onGeometry rev h == s)).count true) =
      ds.count (onGeometry rev s) := by
  induction ds with
  | nil => rfl
  | cons h t ih =>
    cases rev <;> cases s <;> cases h <;> simp_all [onGeometry,RS.swap]

/-- Direction and ties use the lexicographic comparison of the two seed words
of just the first arm. Population imbalance excludes a tie on either geometry. -/
theorem score {i : Input} {l : Reader i} {c : Carrier i i}
    (op : Opposite c l l)
    {f : Site i} (rd : RingGroupedStereo.Ready f l)
    (q : Arm i) (dom : c.domain q) (vq : i.certified.LocalizedRerootCursorValid q)
    (vp : i.certified.LocalizedRerootCursorValid (c.image q)) (oq : q.occurrence.val.root = f.val.root)
    (op' : (c.image q).occurrence.val.root = f.val.root) (rev : Bool) :
    ∃ x y : List Bool, RingFullPathRule5.word? i l rev .R q = some x ∧
      RingFullPathRule5.word? i l rev .S q = some y ∧
      RingFullPathRule5.score? i l rev q (c.image q) =
        some (RingOccurrenceStereo.fixedScore (compare x y) (compare y x)) ∧
      ((donors l q).count .R ≠ (donors l q).count .S → x ≠ y ∧
        (RingFullPathRule5.score? i l rev q (c.image q) = some 2 ∨
         RingFullPathRule5.score? i l rev q (c.image q) = some (-2))) := by
  obtain ⟨_,_,_,_,_,_,_,swap⟩ := words op rd rd q dom vq vp oq op' rev
  obtain ⟨x,hx,ex⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total rd rev [.lowercase]) .R q vq oq
  obtain ⟨y,hy,ey⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total rd rev [.lowercase]) .S q vq oq
  have bx : RingFullPathRule5.word? i l rev .S (c.image q) = some x := (swap true .R).symm.trans hx
  have by' : RingFullPathRule5.word? i l rev .R (c.image q) = some y := (swap true .S).symm.trans hy
  have result : RingFullPathRule5.score? i l rev q (c.image q) =
      some (RingOccurrenceStereo.fixedScore (compare x y) (compare y x)) := by
    simp [RingFullPathRule5.score?,hx,hy,bx,by']
  refine ⟨x,y,hx,hy,result,?_⟩
  intro unequal
  have strict : x ≠ y := by
    intro eqn
    have rx := RingSingleDonorComparison.seed_population rd rev q vq oq .R ((ex _).mpr rfl)
    have sy := RingSingleDonorComparison.seed_population rd rev q vq oq .S ((ey _).mpr rfl)
    rw [eqn] at rx
    have counts := (List.perm_iff_count.mp (rx.symm.trans sy)) true
    rw [count_likes,count_likes] at counts
    cases rev
    · exact unequal counts
    · exact unequal counts.symm
  refine ⟨strict,?_⟩
  rw [result]
  have ne : compare x y ≠ .eq := fun h => strict (Std.compare_eq_eq_iff_eq.mp h)
  have dual : compare y x = (compare x y).swap := (Std.OrientedCmp.eq_swap ..)
  rw [dual]
  cases cmp : compare x y with
  | eq => exact (ne cmp).elim
  | gt => exact Or.inl rfl
  | lt => exact Or.inr rfl

end TetraStereo.Engine.RingOppositeDonorArms
assert_kernel_only TetraStereo.Engine.RingOppositeDonorArms.words
assert_kernel_only TetraStereo.Engine.RingOppositeDonorArms.score
