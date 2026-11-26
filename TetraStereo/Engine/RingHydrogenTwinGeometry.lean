import TetraStereo.Engine.RingHydrogenSpelling
import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation

/-! The public report under independent coordinate changes at identical terminal ligands. -/
set_option autoImplicit false

namespace TetraStereo.Engine.HydrogenPairParity
open OneCenter CertifiedLocalizedCIPInput
open RationalTetrahedralPermutation
open Rule6HandednessSemantics

abbrev Points := Fin 4 → CartesianPoint3

def volume (p : Points) (π : Equiv.Perm (Fin 4)) : ℚ :=
  CartesianPoint3.orientedVolume (p (π 0)) (p (π 1)) (p (π 2)) (p (π 3))

/-- Determinant readback in an arbitrary slot order and either physical reflection. -/
def reading (p : Points) (rev : Bool) (π : Equiv.Perm (Fin 4)) : Option RS :=
  let point := fun k => if rev then (p k).reflectX else p k
  descriptorOfPriorityOrderedPoints? [point (π 0),point (π 1),point (π 2),point (π 3)]

private theorem volume_permutation (p : Points) (π : Equiv.Perm (Fin 4)) :
    volume p π = if RawMolecule.permutationIsEven (finFourPermutationList π) then
      volume p 1 else -volume p 1 := by
  have eta (k : Fin 4) : pointVector (p 0) (p 1) (p 2) (p 3) k = p k := by fin_cases k <;> rfl
  simpa only [permutedOrientedVolume,eta,volume,Equiv.Perm.one_apply] using
    permutedOrientedVolume_eq_if_permutationIsEven (p 0) (p 1) (p 2) (p 3) π

private theorem volume_swap (p : Points) (h k : Fin 4) (ne : h ≠ k) :
    volume p (Equiv.swap h k) = -volume p 1 := by
  have odd : RawMolecule.permutationIsEven (finFourPermutationList (Equiv.swap h k)) = false :=
    (finFourPermutationIsOdd_iff_sign_negOne _).mpr (Equiv.Perm.sign_swap ne)
  rw [volume_permutation,odd]
  rfl

private theorem descriptor_neg (v : ℚ) :
    descriptorOfOrientedVolume? (-v) = (descriptorOfOrientedVolume? v).map RS.swap := by
  rcases lt_trichotomy v 0 with neg | zero | pos
  · simp [RS.swap,descriptorOfOrientedVolume?,neg,neg_pos.mpr neg,not_lt_of_ge (neg_pos.mpr neg).le]
  · simp [zero,descriptorOfOrientedVolume?]
  · simp [RS.swap,descriptorOfOrientedVolume?,pos,not_lt_of_ge pos.le,neg_neg_of_pos pos]

private theorem reading_volume (p : Points) (rev : Bool) (π : Equiv.Perm (Fin 4)) :
    reading p rev π = descriptorOfOrientedVolume? (if rev then -volume p π else volume p π) := by
  cases rev
  · rfl
  · exact congrArg descriptorOfOrientedVolume? (CartesianPoint3.orientedVolume_reflectX _ _ _ _)

/-- One base hand equality propagates to every ordering and reflection. -/
theorem all_orders_of_base (a b : Points)
    (base : descriptorOfOrientedVolume? (volume a 1) = descriptorOfOrientedVolume? (volume b 1)) :
    ∀ π rev, reading a rev π = reading b rev π := by
  intro π rev
  rw [reading_volume a,reading_volume b,volume_permutation a π,volume_permutation b π]
  cases even : RawMolecule.permutationIsEven (finFourPermutationList π) <;>
    cases rev <;> simp [descriptor_neg,base]

/-- At a CH₂, exchange only the two ordinary hydrogens when the two physical
frames have opposite hands. Neither hydrogen coordinates nor initial hand
agreement is assumed. The same repair serves every slot order and reflection. -/
theorem repair_pair (a b : Points) (h k : Fin 4) (ne : h ≠ k)
    (nonzeroA : volume a 1 ≠ 0) (nonzeroB : volume b 1 ≠ 0) :
    ∃ σ : Equiv.Perm (Fin 4),
      (σ = 1 ∨ σ = Equiv.swap h k) ∧
      (∀ t, t ≠ h → t ≠ k → σ t = t) ∧
      ∀ π rev, reading a rev π = reading (fun t => b (σ t)) rev π := by
  have swapBase : volume (fun t => b ((Equiv.swap h k) t)) 1 = -volume b 1 :=
    volume_swap b h k ne
  rcases lt_or_gt_of_ne nonzeroA with an | ap <;>
    rcases lt_or_gt_of_ne nonzeroB with bn | bp
  · refine ⟨1,Or.inl rfl,by simp,all_orders_of_base a b ?_⟩
    simp [descriptorOfOrientedVolume?,an,bn]
  · refine ⟨Equiv.swap h k,Or.inr rfl,?_,all_orders_of_base a _ ?_⟩
    · intro t th tk
      exact Equiv.swap_apply_of_ne_of_ne th tk
    · rw [swapBase]
      simp [descriptorOfOrientedVolume?,an,neg_neg_of_pos bp]
  · refine ⟨Equiv.swap h k,Or.inr rfl,?_,all_orders_of_base a _ ?_⟩
    · intro t th tk
      exact Equiv.swap_apply_of_ne_of_ne th tk
    · rw [swapBase]
      simp [descriptorOfOrientedVolume?,ap,not_lt_of_ge ap.le,neg_pos.mpr bn,
        not_lt_of_ge (neg_pos.mpr bn).le]
  · refine ⟨1,Or.inl rfl,by simp,all_orders_of_base a b ?_⟩
    simp [descriptorOfOrientedVolume?,ap,bp,not_lt_of_ge ap.le,not_lt_of_ge bp.le]

/-- Standard CH₂ frame: slots 0 and 1 are heavy, slots 2 and 3 are ordinary H. -/
theorem repair_ch2 (a b : Points) (nonzeroA : volume a 1 ≠ 0) (nonzeroB : volume b 1 ≠ 0) :
    ∃ σ : Equiv.Perm (Fin 4), (σ = 1 ∨ σ = Equiv.swap 2 3) ∧ σ 0 = 0 ∧ σ 1 = 1 ∧
      ∀ π rev, reading a rev π = reading (fun t => b (σ t)) rev π := by
  obtain ⟨σ,choice,fixed,reads⟩ := repair_pair a b 2 3 (by decide) nonzeroA nonzeroB
  exact ⟨σ,choice,fixed 0 (by decide) (by decide),fixed 1 (by decide) (by decide),reads⟩
open LocalizedGenericMarkedRecalculation (Geometry readback? mirror)

def atomOrder (ids : Fin 4 → Nat) (π : Equiv.Perm (Fin 4)) : List Nat :=
  [ids (π 0),ids (π 1),ids (π 2),ids (π 3)]

private theorem readback_points (geom : Geometry) (ids : Fin 4 → Nat) (p : Points)
    (coordinates : ∀ k, geom (ids k) = some (p k)) (π : Equiv.Perm (Fin 4)) (rev : Bool) :
    readback? (if rev then mirror geom else geom) (atomOrder ids π) = reading p rev π := by
  have plain : readback? geom (atomOrder ids π) = reading p false π := by
    simp only [readback?,atomOrder,List.mapM_cons,coordinates]
    rfl
  cases rev
  · exact plain
  · simp only [Bool.false_eq_true,if_false,if_true,LocalizedGenericMarkedRecalculation.readback_mirror,plain,
      reading_volume,descriptor_neg]

/-- Geometry-level bridge: the same ordinary-H exchange matches every actual
readback in every order, both before and after spatial reflection. -/
theorem repair_readbacks (first second : Geometry) (idsA idsB : Fin 4 → Nat)
    (a b : Points) (coordinatesA : ∀ k, first (idsA k) = some (a k))
    (coordinatesB : ∀ k, second (idsB k) = some (b k))
    (h k : Fin 4) (ne : h ≠ k) (nonzeroA : volume a 1 ≠ 0) (nonzeroB : volume b 1 ≠ 0) :
    ∃ σ : Equiv.Perm (Fin 4),
      (σ = 1 ∨ σ = Equiv.swap h k) ∧ (∀ t, t ≠ h → t ≠ k → σ t = t) ∧
      ∀ (π : Equiv.Perm (Fin 4)) (rev : Bool),
        readback? (if rev then mirror first else first) (atomOrder idsA π) =
        readback? (if rev then mirror second else second) (atomOrder (fun t => idsB (σ t)) π) := by
  obtain ⟨σ,choice,fixed,reads⟩ := repair_pair a b h k ne nonzeroA nonzeroB
  refine ⟨σ,choice,fixed,fun π rev => ?_⟩
  rw [readback_points first idsA a coordinatesA,
    readback_points second (fun t => idsB (σ t)) (fun t => b (σ t)) (fun t => coordinatesB (σ t))]
  exact reads π rev
end TetraStereo.Engine.HydrogenPairParity
assert_kernel_only TetraStereo.Engine.HydrogenPairParity.repair_pair
assert_kernel_only TetraStereo.Engine.HydrogenPairParity.repair_ch2

assert_kernel_only TetraStereo.Engine.HydrogenPairParity.repair_readbacks

namespace TetraStereo.Engine.HydrogenLeafParity
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingSpatialTransport
open RingNumberedHydrogenGeometry
open HydrogenPairParity (volume atomOrder)
open RingWrittenPHReadings (geometry)

/-- The four actual points selected from a full replacement coordinate table. -/
def framePoints (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
    (ids : Fin 4 → i.certified.Atom) : HydrogenPairParity.Points :=
  fun t => sourcePoint (atGeometry i g full) (ids t)

private theorem points_lookup (i : Input) (g : SpatialConfiguration)
    (full : g.positions.length = size i) (ids : Fin 4 → i.certified.Atom) (t : Fin 4) :
    geometry g (ids t).val = some (framePoints i g full ids t) :=
  sourcePoint_lookup (i := atGeometry i g full) (ids t)

private theorem swap_outside (i : Input) (w : SpatialConfiguration)
    (full : w.positions.length = size i) (u v : i.certified.Atom)
    (e : Equiv.Perm i.certified.Atom) (choice : e = 1 ∨ e = Equiv.swap u v)
    (n : Nat) (nu : n ≠ u.val) (nv : n ≠ v.val) :
    (reindexed (atGeometry i w full) i e).positions[n]? = w.positions[n]? := by
  by_cases bound : n < size i
  · let a : i.certified.Atom := ⟨n,bound⟩
    have au : a ≠ u := fun eq => nu (congrArg Fin.val eq)
    have av : a ≠ v := fun eq => nv (congrArg Fin.val eq)
    have fixed : e.symm a = a := by
      rcases choice with rfl | rfl
      · rfl
      · exact Equiv.swap_apply_of_ne_of_ne au av
    have lookup := reindexed_lookup (i := atGeometry i w full) (j := i) e a
    exact lookup.trans (congrArg (fun b : i.certified.Atom => w.positions[b.val]?) fixed)
  · have wn : w.positions[n]? = none := List.getElem?_eq_none (by rw [full]; omega)
    have rn : (reindexed (atGeometry i w full) i e).positions[n]? = none :=
      List.getElem?_eq_none (by rw [reindexed_full]; omega)
    exact rn.trans wn.symm

/-- Local CH₂ sign repair realized by a permutation of actual atom IDs.
Only the two designated leaves can move. The same actual permutation serves
all priority orders and both spatial reflections of this one tetra frame. -/
theorem select_leaf_parity (i : Input) (w x : SpatialConfiguration)
    (fullW : w.positions.length = size i) (fullX : x.positions.length = size i)
    (ids : Fin 4 → i.certified.Atom) (injective : Function.Injective ids)
    (u v : i.certified.Atom) (different : u ≠ v)
    (h k : Fin 4) (atU : ids h = u) (atV : ids k = v)
    (nonzeroW : volume (framePoints i w fullW ids) 1 ≠ 0)
    (nonzeroX : volume (framePoints i x fullX ids) 1 ≠ 0) :
    ∃ e : Equiv.Perm i.certified.Atom,
      (e = 1 ∨ e = Equiv.swap u v) ∧
      (∀ n, n ≠ u.val → n ≠ v.val →
        (reindexed (atGeometry i w fullW) i e).positions[n]? = w.positions[n]?) ∧
      ∀ (π : Equiv.Perm (Fin 4)) (rev : Bool),
        readback? (if rev then mirror (geometry x) else geometry x)
          (atomOrder (fun t => (ids t).val) π) =
        readback? (if rev then mirror (geometry (reindexed (atGeometry i w fullW) i e))
          else geometry (reindexed (atGeometry i w fullW) i e))
          (atomOrder (fun t => (ids t).val) π) := by
  have hk : h ≠ k := by intro eq; exact different (atU.symm.trans ((congrArg ids eq).trans atV))
  obtain ⟨σ,choice,_,reads⟩ := HydrogenPairParity.repair_readbacks (geometry x) (geometry w)
    (fun t => (ids t).val) (fun t => (ids t).val)
    (framePoints i x fullX ids) (framePoints i w fullW ids)
    (points_lookup i x fullX ids) (points_lookup i w fullW ids) h k hk nonzeroX nonzeroW
  have selected : ∃ e : Equiv.Perm i.certified.Atom,
      (e = 1 ∨ e = Equiv.swap u v) ∧ ∀ t, e.symm (ids t) = ids (σ t) := by
    rcases choice with rfl | rfl
    · exact ⟨1,Or.inl rfl,fun _ => rfl⟩
    · refine ⟨Equiv.swap u v,Or.inr rfl,fun t => ?_⟩
      rw [← atU,← atV]
      exact injective.swap_apply h k t
  obtain ⟨e,choice,action⟩ := selected
  refine ⟨e,choice,swap_outside i w fullW u v e choice,fun π rev => ?_⟩
  have pulled (t : Fin 4) : geometry (reindexed (atGeometry i w fullW) i e) (ids t).val =
      geometry w (ids (σ t)).val := by
    change (reindexed (atGeometry i w fullW) i e).positions[(ids t).val]? = _
    exact (reindexed_lookup (i := atGeometry i w fullW) (j := i) e (ids t)).trans
      (congrArg (fun a : i.certified.Atom => w.positions[a.val]?) (action t))
  have plain : readback? (geometry (reindexed (atGeometry i w fullW) i e))
      (atomOrder (fun t => (ids t).val) π) =
      readback? (geometry w) (atomOrder (fun t => (ids (σ t)).val) π) := by
    simp only [readback?,atomOrder,List.mapM_cons,List.mapM_nil,pulled]
  have pulledRead : readback? (if rev then mirror (geometry (reindexed (atGeometry i w fullW) i e))
      else geometry (reindexed (atGeometry i w fullW) i e)) (atomOrder (fun t => (ids t).val) π) =
      readback? (if rev then mirror (geometry w) else geometry w)
        (atomOrder (fun t => (ids (σ t)).val) π) := by
    cases rev <;> simp only [Bool.false_eq_true,if_false,if_true,readback_mirror,plain]
  exact (reads π rev).trans pulledRead.symm

/-- Canonical-frame specialization for an actual detected tetrahedral center. -/
theorem select_canonical_leaf_parity (i : Input) (w x : SpatialConfiguration)
    (fullW : w.positions.length = size i) (fullX : x.positions.length = size i)
    (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) (different : u ≠ v)
    (h k : Fin 4) (atU : i.certified.canonicalLigandAtom c h = u)
    (atV : i.certified.canonicalLigandAtom c k = v)
    (nonzeroW : volume (framePoints i w fullW (i.certified.canonicalLigandAtom c)) 1 ≠ 0)
    (nonzeroX : volume (framePoints i x fullX (i.certified.canonicalLigandAtom c)) 1 ≠ 0) :
    ∃ e : Equiv.Perm i.certified.Atom,
      (e = 1 ∨ e = Equiv.swap u v) ∧
      (∀ n, n ≠ u.val → n ≠ v.val →
        (reindexed (atGeometry i w fullW) i e).positions[n]? = w.positions[n]?) ∧
      ∀ (π : Equiv.Perm (Fin 4)) (rev : Bool),
        readback? (if rev then mirror (geometry x) else geometry x)
          (atomOrder (fun t => (i.certified.canonicalLigandAtom c t).val) π) =
        readback? (if rev then mirror (geometry (reindexed (atGeometry i w fullW) i e))
          else geometry (reindexed (atGeometry i w fullW) i e))
          (atomOrder (fun t => (i.certified.canonicalLigandAtom c t).val) π) :=
  select_leaf_parity i w x fullW fullX (i.certified.canonicalLigandAtom c)
    (i.certified.canonicalLigandAtom_injective c) u v different h k atU atV nonzeroW nonzeroX
end TetraStereo.Engine.HydrogenLeafParity
assert_kernel_only TetraStereo.Engine.HydrogenLeafParity.select_leaf_parity
assert_kernel_only TetraStereo.Engine.HydrogenLeafParity.select_canonical_leaf_parity

namespace TetraStereo.Engine.RingHydrogenLeafGeometry
open OneCenter
open LocalizedChemicalRing (Input)
open RingWrittenPHReadings
open RingPyramidalChoices (phosphorusFrameIds)
open LocalizedGenericMarkedRecalculation (readback?)
variable {i : Input}

/-- The leaf's only physical neighbor is its supporting atom. -/
def SupportedLeaf (i : Input) (leaf parent : i.certified.Atom) : Prop :=
  ∀ b, i.certified.moleculeGraph.Adj leaf b ↔ b = parent

theorem SupportedLeaf.degree_one {u c : i.certified.Atom} (leaf : SupportedLeaf i u c) :
    Fintype.card (i.certified.moleculeGraph.Neighbor u) = 1 := by
  let e : i.certified.moleculeGraph.Neighbor u ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨c,(leaf c).mpr rfl⟩
      left_inv := fun n => Subtype.ext ((leaf n.val).mp n.property).symm
      right_inv := fun x => by cases x; rfl }
  simpa using Fintype.card_congr e

theorem phosphorus_ne_leaf {u c a : i.certified.Atom} (leaf : SupportedLeaf i u c)
    (hp : RingPyramidalPublication.phosphorus i a = true) : a ≠ u := by
  intro eq
  subst a
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor u) = 3 := by
    simp only [RingPyramidalPublication.phosphorus,Bool.and_eq_true,decide_eq_true_eq] at hp
    exact hp.2
  have one := leaf.degree_one
  omega

variable {u v c : i.certified.Atom} {w x : SpatialConfiguration}

theorem neighbor_avoids_leaf (leaf : SupportedLeaf i u c) {a : i.certified.Atom}
    (away : a ≠ c) (b : i.certified.moleculeGraph.Neighbor a) : b.val ≠ u := by
  intro eq
  have edge := b.property
  rw [eq] at edge
  exact away ((leaf a).mp ((i.certified.moleculeGraph.adj_symm).mp edge))

/-- Every tetrahedral hand away from the common support is unchanged, in every
neighbor enumeration and slot order, including reflected or degenerate frames. -/
theorem tetra_away (lu : SupportedLeaf i u c) (lv : SupportedLeaf i v c)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (b : i.certified.TetrahedralCenter) (away : b.val ≠ c)
    (d : Fin 4 ≃ i.certified.moleculeGraph.Neighbor b.val) (rev : Bool) (π : Equiv.Perm (Fin 4)) :
    readback? (oriented w rev) (order (fun k => (d k).val.val) π) =
      readback? (oriented x rev) (order (fun k => (d k).val.val) π) := by
  have point (k : Fin 4) : geometry w (d k).val.val = geometry x (d k).val.val :=
    fixed (d k).val (neighbor_avoids_leaf lu away (d k)) (neighbor_avoids_leaf lv away (d k))
  have plain : readback? (geometry w) (order (fun k => (d k).val.val) π) =
      readback? (geometry x) (order (fun k => (d k).val.val) π) := by
    apply RingFrameTransport.readback_congr
    intro n hn
    simp only [order,List.mem_cons,List.mem_nil_iff,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> exact point _
  cases rev <;> simp [oriented,LocalizedGenericMarkedRecalculation.readback_mirror,plain]

/-- Leaf motion cannot change any phosphorus determinant. The proof includes the
phosphorus/phantom slot itself, using degree three to exclude either moved leaf. -/
theorem phosphorus_all (lu : SupportedLeaf i u c) (lv : SupportedLeaf i v c)
    (notP : RingPyramidalPublication.phosphorus i c = false)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (a : i.certified.Atom) (hp : RingPyramidalPublication.phosphorus i a = true)
    (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) (rev : Bool) :
    readback? (oriented w rev) (order (phosphorusFrameIds d) 1) =
      readback? (oriented x rev) (order (phosphorusFrameIds d) 1) := by
  have away : a ≠ c := by intro eq; subst a; rw [notP] at hp; contradiction
  have point (k : Fin 3) : geometry w (d k).val.val = geometry x (d k).val.val :=
    fixed (d k).val (neighbor_avoids_leaf lu away (d k)) (neighbor_avoids_leaf lv away (d k))
  have center : geometry w a.val = geometry x a.val :=
    fixed a (phosphorus_ne_leaf lu hp) (phosphorus_ne_leaf lv hp)
  have plain : readback? (geometry w) (order (phosphorusFrameIds d) 1) =
      readback? (geometry x) (order (phosphorusFrameIds d) 1) := by
    change readback? (geometry w) [(d 0).val.val,(d 1).val.val,(d 2).val.val,a.val] =
      readback? (geometry x) [(d 0).val.val,(d 1).val.val,(d 2).val.val,a.val]
    apply RingFrameTransport.readback_congr
    intro n hn
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact point 0
    · exact point 1
    · exact point 2
    · exact center
  cases rev <;> simp [oriented,LocalizedGenericMarkedRecalculation.readback_mirror,plain]

/-- Only the supported tetrahedral centre remains to be checked after moving
its two terminal leaves. All other physical hands follow from fixed coordinates. -/
theorem physicalAgreement_of_support (lu : SupportedLeaf i u c) (lv : SupportedLeaf i v c)
    (notP : RingPyramidalPublication.phosphorus i c = false)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (support : ∀ b : i.certified.TetrahedralCenter, b.val = c →
      ∀ (d : Fin 4 ≃ i.certified.moleculeGraph.Neighbor b.val) rev π,
      readback? (oriented w rev) (order (fun k => (d k).val.val) π) =
      readback? (oriented x rev) (order (fun k => (d k).val.val) π)) : PhysicalAgreement i w x := by
  constructor
  · intro b d rev π
    by_cases same : b.val = c
    · exact support b same d rev π
    · exact tetra_away lu lv fixed b same d rev π
  · exact phosphorus_all lu lv notP fixed

theorem notP_of_degree_four (c : i.certified.Atom)
    (four : Fintype.card (i.certified.moleculeGraph.Neighbor c) = 4) :
    RingPyramidalPublication.phosphorus i c = false := by
  cases hp : RingPyramidalPublication.phosphorus i c with
  | false => rfl
  | true =>
    simp only [RingPyramidalPublication.phosphorus,Bool.and_eq_true,decide_eq_true_eq] at hp
    omega

/-- Degree four alone excludes the supporting atom from the P rule; no atom-record
or source-coordinate hypothesis is needed for the unaffected-frame argument. -/
theorem physicalAgreement_of_degree_four_support
    (lu : SupportedLeaf i u c) (lv : SupportedLeaf i v c)
    (four : Fintype.card (i.certified.moleculeGraph.Neighbor c) = 4)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (support : ∀ b : i.certified.TetrahedralCenter, b.val = c →
      ∀ (d : Fin 4 ≃ i.certified.moleculeGraph.Neighbor b.val) rev π,
      readback? (oriented w rev) (order (fun k => (d k).val.val) π) =
      readback? (oriented x rev) (order (fun k => (d k).val.val) π)) : PhysicalAgreement i w x :=
  physicalAgreement_of_support lu lv (notP_of_degree_four c four) fixed support

end TetraStereo.Engine.RingHydrogenLeafGeometry
assert_kernel_only TetraStereo.Engine.RingHydrogenLeafGeometry.tetra_away
assert_kernel_only TetraStereo.Engine.RingHydrogenLeafGeometry.phosphorus_all
assert_kernel_only TetraStereo.Engine.RingHydrogenLeafGeometry.physicalAgreement_of_support
assert_kernel_only TetraStereo.Engine.RingHydrogenLeafGeometry.physicalAgreement_of_degree_four_support

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)
variable {i : Input}

/-- Exchanging two terminal atoms with identical molecular records and the same
single-bond parent preserves every atom datum and bond order used by the report. -/
def twinSwap (u v c : i.certified.Atom)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c then 1 else 0) : GraphMap i i := by
  let e := Equiv.swap u v
  have exchange (a b : i.certified.Atom) : i.molecule.bondOrder (e a).val b.val = i.molecule.bondOrder a.val b.val := by
    by_cases h : a = u
    · subst a; simp [e,lu,lv]
    by_cases k : a = v
    · subst a; simp [e,lu,lv]
    rw [show e a = a from Equiv.swap_apply_of_ne_of_ne h k]
  refine ⟨e,?_,?_⟩
  · intro a
    by_cases h : a = u
    · subst a; simpa [e] using records.symm
    by_cases k : a = v
    · subst a; simpa [e] using records
    rw [show e a = a from Equiv.swap_apply_of_ne_of_ne h k]
  · intro a b
    rw [exchange,i.molecule.bondOrder_symm a.val (e b).val,exchange,i.molecule.bondOrder_symm]

def identityGraph (i : Input) : GraphMap i i := ⟨Equiv.refl _,fun _ => rfl,fun _ _ => rfl⟩

theorem graph_of_twin_choice (u v c : i.certified.Atom)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c then 1 else 0)
    (e : Equiv.Perm i.certified.Atom) (choice : e = 1 ∨ e = Equiv.swap u v) :
    ∃ g : GraphMap i i, g.atoms = e := by
  rcases choice with rfl | rfl
  · exact ⟨identityGraph i,rfl⟩
  · exact ⟨twinSwap u v c records lu lv,rfl⟩

end TetraStereo.Engine.RingHydrogenSpelling

namespace TetraStereo.Engine.LeafAllRequests
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenSpelling (moveId)
private def moveRow {n : Nat} (e : Equiv.Perm (Fin n)) (row : Nat × Option RingNestedActivePair.Labels) :=
  (moveId e row.1,row.2)

/-- Every structurally ineligible original atom receives a completed refusal. -/
theorem root_ineligible (i : Input) (a : i.certified.Atom)
    (no : RingPyramidalPublication.eligible i a = false) :
    RingChemicalGraphProof.root i a = some none := by
  unfold RingChemicalGraphProof.root
  rw [RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
    RingActiveDistanceSchedule.evaluate_eq]
  apply RingChemicalGraphProof.skips i
  rintro ⟨_,b,located,allowed⟩
  have ab : a = b := Option.some.inj ((RingGroupedReport.origin_address i a).2.2.symm.trans located)
  subst b
  rw [no] at allowed
  contradiction

theorem terminal_ineligible (i : Input) (a : i.certified.Atom)
    (degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 1) :
    RingPyramidalPublication.eligible i a = false := by
  simp [RingPyramidalPublication.eligible,RingPyramidalPublication.phosphorus,degree]

/-- Fixing nonterminal vertices also fixes them under the inverse permutation. -/
theorem inverse_fixes_nonterminal (i : Input) (e : Equiv.Perm i.certified.Atom)
    (fixed : ∀ a, Fintype.card (i.certified.moleculeGraph.Neighbor a) ≠ 1 → e a = a) :
    ∀ a, Fintype.card (i.certified.moleculeGraph.Neighbor a) ≠ 1 → e.symm a = a := by
  intro a ha
  simpa only [Equiv.symm_apply_apply] using (congrArg e.symm (fixed a ha)).symm

/-- A permutation supported on terminal vertices preserves every native root value. -/
theorem root_permutation_of_nonterminal_fixed (i : Input) (e : Equiv.Perm i.certified.Atom)
    (fixed : ∀ a, Fintype.card (i.certified.moleculeGraph.Neighbor a) ≠ 1 → e a = a)
    (a : i.certified.Atom) :
    RingChemicalGraphProof.root i (e a) = RingChemicalGraphProof.root i a := by
  by_cases same : e a = a
  · rw [same]
  · have degreeA : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 1 := by
      by_contra notleaf
      exact same (fixed a notleaf)
    have degreeE : Fintype.card (i.certified.moleculeGraph.Neighbor (e a)) = 1 := by
      by_contra notleaf
      have eq := inverse_fixes_nonterminal i e fixed (e a) notleaf
      exact same (by simpa only [Equiv.symm_apply_apply] using eq.symm)
    rw [root_ineligible i a (terminal_ineligible i a degreeA),
      root_ineligible i (e a) (terminal_ineligible i (e a) degreeE)]

private theorem root_swap (i : Input) (u v : i.certified.Atom) (e : Equiv.Perm i.certified.Atom)
    (choice : e = 1 ∨ e = Equiv.swap u v)
    (ru : RingChemicalGraphProof.root i u = some none)
    (rv : RingChemicalGraphProof.root i v = some none) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i (e a) = RingChemicalGraphProof.root i a := by
  rcases choice with rfl | rfl
  · rfl
  · by_cases au : a = u
    · subst a; simp only [Equiv.swap_apply_left,ru,rv]
    · by_cases av : a = v
      · subst a; simp only [Equiv.swap_apply_right,ru,rv]
      · rw [Equiv.swap_apply_of_ne_of_ne au av]

/-- Report locality for any permutation preserving the native root readings. -/
theorem typed_report_permutation (i : Input) (e : Equiv.Perm i.certified.Atom)
    (roots : ∀ a, RingChemicalGraphProof.root i (e a) = RingChemicalGraphProof.root i a)
    (atoms : List i.certified.Atom) :
    RingChemicalReport.report? i (atoms.map e) =
      (RingChemicalReport.report? i atoms).map (List.map (moveRow e)) := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    simp only [RingChemicalReport.report?,List.map_cons,List.mapM_cons]
    change (do
      let v ← (RingChemicalGraphProof.root i (e a)).map (fun l => ((e a).val,l))
      let vs ← RingChemicalReport.report? i (atoms.map e)
      pure (v :: vs)) = Option.map _ (do
        let v ← (RingChemicalGraphProof.root i a).map (fun l => (a.val,l))
        let vs ← RingChemicalReport.report? i atoms
        pure (v :: vs))
    rw [roots a,ih]
    cases RingChemicalGraphProof.root i a <;> cases RingChemicalReport.report? i atoms <;>
      simp [moveRow,moveId,a.isLt]

/-- Report locality: swapping two refusal-only query atoms just relabels rows. -/
theorem typed_report_swap (i : Input) (u v : i.certified.Atom) (e : Equiv.Perm i.certified.Atom)
    (choice : e = 1 ∨ e = Equiv.swap u v)
    (ru : RingChemicalGraphProof.root i u = some none)
    (rv : RingChemicalGraphProof.root i v = some none) (atoms : List i.certified.Atom) :
    RingChemicalReport.report? i (atoms.map e) =
      (RingChemicalReport.report? i atoms).map (List.map (moveRow e)) :=
  typed_report_permutation i e (root_swap i u v e choice ru rv) atoms

private theorem bound_move (i : Input) (e : Equiv.Perm i.certified.Atom) (n : Nat) :
    moveId e n < i.molecule.atomCount ↔ n < i.molecule.atomCount := by
  have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  unfold moveId
  split
  · rename_i h
    exact iff_of_true (size ▸ (e ⟨n,h⟩).isLt) (size ▸ h)
  · rfl

private theorem rejected (i : Input) (closed : RingHydrogenCompletion.plan i.molecule = []) (ids : List Nat)
    (bad : ¬((∀ n ∈ ids, n < i.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted i = true)) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids = none := by
  cases got : RingHydrogenReport.fromRaw? i.molecule i.spatial ids with
  | none => rfl
  | some rows =>
    rw [RingHydrogenReport.fromRaw_closed_eq closed] at got
    exact (bad ((RingSpatialTransport.closed_domain i closed ids).mp ⟨rows,got⟩)).elim

/-- Native root preservation gives report equivariance for all Nat requests,
including invalid IDs and failed coordinate admission. -/
theorem raw_report_preserving_roots (i : Input) (closed : RingHydrogenCompletion.plan i.molecule = [])
    (e : Equiv.Perm i.certified.Atom)
    (roots : ∀ a, RingChemicalGraphProof.root i (e a) = RingChemicalGraphProof.root i a)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial (ids.map (moveId e)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map (List.map (moveRow e)) := by
  by_cases ok : (∀ n ∈ ids, n < i.molecule.atomCount) ∧ LocalizedChemicalRing.coordinatesAdmitted i = true
  · have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
    let atoms : List i.certified.Atom := ids.attach.map fun n => ⟨n.val,by rw [size]; exact ok.1 _ n.property⟩
    have raw : atoms.map Fin.val = ids := by simp [atoms,List.map_map,Function.comp_def]
    have moved : (atoms.map e).map Fin.val = ids.map (moveId e) := by
      rw [←raw]
      have valMove (a : i.certified.Atom) : moveId e a.val = (e a).val := by simp [moveId,a.isLt]
      simp only [List.map_map,Function.comp_def,valMove]
    rw [←moved,←raw,RingWrittenPHReadings.fromRaw_closed_report i closed ok.2,
      RingWrittenPHReadings.fromRaw_closed_report i closed ok.2]
    exact typed_report_permutation i e roots atoms
  · have bad : ¬((∀ n ∈ ids.map (moveId e), n < i.molecule.atomCount) ∧
        LocalizedChemicalRing.coordinatesAdmitted i = true) := by
      simpa only [List.forall_mem_map,bound_move] using ok
    rw [rejected i closed ids ok,rejected i closed _ bad]
    rfl

/-- Source responses are equivariant for all Nat requests, including invalid
IDs and failed coordinate admission, when the exchanged atoms are refusals. -/
theorem raw_report_swap (i : Input) (closed : RingHydrogenCompletion.plan i.molecule = [])
    (u v : i.certified.Atom) (e : Equiv.Perm i.certified.Atom)
    (choice : e = 1 ∨ e = Equiv.swap u v)
    (ru : RingChemicalGraphProof.root i u = some none)
    (rv : RingChemicalGraphProof.root i v = some none) (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial (ids.map (moveId e)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map (List.map (moveRow e)) :=
  raw_report_preserving_roots i closed e (root_swap i u v e choice ru rv) ids

/-- Arbitrary permutations supported on terminal vertices preserve every raw response. -/
theorem raw_report_permutation (i : Input) (closed : RingHydrogenCompletion.plan i.molecule = [])
    (e : Equiv.Perm i.certified.Atom)
    (fixed : ∀ a, Fintype.card (i.certified.moleculeGraph.Neighbor a) ≠ 1 → e a = a)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial (ids.map (moveId e)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map (List.map (moveRow e)) :=
  raw_report_preserving_roots i closed e (root_permutation_of_nonterminal_fixed i e fixed) ids

theorem moveId_involutive {n : Nat} (u v : Fin n) (e : Equiv.Perm (Fin n))
    (choice : e = 1 ∨ e = Equiv.swap u v) : Function.Involutive (moveId e) := by
  intro a
  by_cases bound : a < n
  · have eb : (e ⟨a,bound⟩).val < n := (e ⟨a,bound⟩).isLt
    simp only [moveId,dif_pos bound,dif_pos eb]
    rcases choice with rfl | rfl
    · rfl
    · exact congrArg Fin.val (Equiv.swap_apply_self u v ⟨a,bound⟩)
  · simp only [moveId,dif_neg bound]

/-- All original Nat requests agree after the local leaf-parity repair.
Direct requests on either swapped H are completed refusals; arbitrary
multiplicities, ordering, invalid IDs and coordinate rejection are retained. -/
theorem all_original_ids (i : Input) (x : SpatialConfiguration)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (u v : i.certified.Atom)
    (degreeU : Fintype.card (i.certified.moleculeGraph.Neighbor u) = 1)
    (degreeV : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 1)
    (e : Equiv.Perm i.certified.Atom) (choice : e = 1 ∨ e = Equiv.swap u v)
    (transport : ∀ ids, RingHydrogenReport.fromRaw? i.molecule x (ids.map (moveId e)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map (List.map (moveRow e))) (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule i.spatial ids := by
  have invol := moveId_involutive u v e choice
  have twice : (ids.map (moveId e)).map (moveId e) = ids := by
    rw [List.map_map]
    calc
      ids.map (moveId e ∘ moveId e) = ids.map id := List.map_congr_left fun a _ => invol a
      _ = ids := List.map_id ids
  have rowTwice : ∀ row : Nat × Option RingNestedActivePair.Labels, moveRow e (moveRow e row) = row := by
    intro row
    exact Prod.ext (invol row.1) rfl
  have changed := transport (ids.map (moveId e))
  rw [twice,raw_report_swap i closed u v e choice
    (root_ineligible i u (terminal_ineligible i u degreeU))
    (root_ineligible i v (terminal_ineligible i v degreeV)) ids] at changed
  simpa [Option.map_map,List.map_map,Function.comp_def,rowTwice] using changed
/-- The total Nat-ID extension of an atom permutation has its actual inverse,
including on invalid IDs, which both maps leave untouched. -/
theorem moveId_apply_inverse {n : Nat} (e : Equiv.Perm (Fin n)) (a : Nat) :
    moveId e (moveId e.symm a) = a := by
  by_cases bound : a < n
  · have eb : (e.symm ⟨a,bound⟩).val < n := (e.symm ⟨a,bound⟩).isLt
    simp only [moveId,dif_pos bound,dif_pos eb]
    exact congrArg Fin.val (e.apply_symm_apply ⟨a,bound⟩)
  · simp only [moveId,dif_neg bound]

/-- Arbitrarily many independent terminal-H permutations disappear from the
public response on every original Nat request. No involution, valid-ID,
coordinate-admission, or successful-response assumption is required. -/
theorem all_original_ids_many (i : Input) (x : SpatialConfiguration)
    (closed : RingHydrogenCompletion.plan i.molecule = [])
    (e : Equiv.Perm i.certified.Atom)
    (fixed : ∀ a, Fintype.card (i.certified.moleculeGraph.Neighbor a) ≠ 1 → e a = a)
    (transport : ∀ ids, RingHydrogenReport.fromRaw? i.molecule x (ids.map (moveId e)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map
        (List.map fun row => (moveId e row.1,row.2))) (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule i.spatial ids := by
  let original := ids.map (moveId e.symm)
  have restored : original.map (moveId e) = ids := by
    simp only [original,List.map_map,Function.comp_def,moveId_apply_inverse,List.map_id']
  have changed := transport original
  have source := raw_report_permutation i closed e fixed original
  rw [restored] at changed source
  exact changed.trans source.symm
end TetraStereo.Engine.LeafAllRequests
assert_kernel_only TetraStereo.Engine.LeafAllRequests.raw_report_swap
assert_kernel_only TetraStereo.Engine.LeafAllRequests.all_original_ids

assert_kernel_only TetraStereo.Engine.LeafAllRequests.root_permutation_of_nonterminal_fixed
assert_kernel_only TetraStereo.Engine.LeafAllRequests.typed_report_permutation
assert_kernel_only TetraStereo.Engine.LeafAllRequests.raw_report_preserving_roots
assert_kernel_only TetraStereo.Engine.LeafAllRequests.raw_report_permutation
assert_kernel_only TetraStereo.Engine.LeafAllRequests.all_original_ids_many

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)
open RingWrittenPHReadings RingSpatialTransport RingNumberedHydrogenGeometry
open RingHydrogenLeafGeometry HydrogenLeafParity
variable {i : Input}

theorem supported_of_bond_row {u c : i.certified.Atom}
    (leaf : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c then 1 else 0) :
    SupportedLeaf i u c := by
  intro a
  rw [LocalizedChemicalRingPhysicalSense.adj_iff i.molecule i.certified i.agreement
    i.admissible.1.1 i.admissible.1.2 i.supported u a,leaf]
  split <;> simp_all

theorem admitted_nonzero (g : SpatialConfiguration) (full : g.positions.length = size i)
    (c : i.certified.TetrahedralCenter) (admit : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i g full) = true) :
    HydrogenPairParity.volume (framePoints i g full (i.certified.canonicalLigandAtom c)) 1 ≠ 0 := by
  let j := atGeometry i g full
  obtain ⟨v,hv,nz⟩ := (LocalizedChemicalRingPhysicalAdmission.allCentersAdmitted_iff j.certified).mp admit c
  rw [coordinateVolume_eq] at hv
  change pointVolume g (fun k => (i.certified.canonicalLigandAtom c k).val) = some v at hv
  have point (k : Fin 4) : g.positions[(i.certified.canonicalLigandAtom c k).val]? =
      some (framePoints i g full (i.certified.canonicalLigandAtom c) k) :=
    sourcePoint_lookup (i := j) (i.certified.canonicalLigandAtom c k)
  simp only [pointVolume,point] at hv
  exact fun zero => nz ((Option.some.inj hv).symm.trans zero)

/-- Moving two identical terminal ligands can reverse the determinant in a fixed
written H order. One exchange of the two leaf identifiers restores all actual
and reflected frame readings simultaneously, at every center of the molecule. -/
theorem twin_coordinate_match (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) (ne : u ≠ v)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (nw : HydrogenPairParity.volume (framePoints i w hw (i.certified.canonicalLigandAtom c)) 1 ≠ 0)
    (nx : HydrogenPairParity.volume (framePoints i x hx (i.certified.canonicalLigandAtom c)) 1 ≠ 0) :
    ∃ g : GraphMap i i, (g.atoms = 1 ∨ g.atoms = Equiv.swap u v) ∧ ReadingMatch g w x := by
  have su := supported_of_bond_row lu
  have sv := supported_of_bond_row lv
  let d := tetraEnumeration i c
  obtain ⟨h,hu⟩ := d.surjective ⟨u,i.certified.moleculeGraph.adj_symm.mpr ((su c.val).mpr rfl)⟩
  obtain ⟨k,hv⟩ := d.surjective ⟨v,i.certified.moleculeGraph.adj_symm.mpr ((sv c.val).mpr rfl)⟩
  obtain ⟨e,choice,unchanged,matchC⟩ := select_canonical_leaf_parity i w x hw hx c u v ne h k
    (congrArg Subtype.val hu) (congrArg Subtype.val hv) nw nx
  obtain ⟨g,hg⟩ := graph_of_twin_choice u v c.val records lu lv e choice
  refine ⟨g,hg ▸ choice,hw,?_⟩
  rw [hg]
  have outside (a : i.certified.Atom) (au : a ≠ u) (av : a ≠ v) :
      x.positions[a.val]? = (reindexed (atGeometry i w hw) i e).positions[a.val]? :=
    (fixed a au av).symm.trans ((unchanged a.val (fun h => au (Fin.ext h)) (fun h => av (Fin.ext h))).symm)
  constructor
  · intro b
    by_cases same : b.val = c.val
    · obtain rfl := Subtype.ext same
      exact matchC 1 false
    · exact tetra_away su sv outside b same (tetraEnumeration i b) false 1
  · intro a hp
    exact phosphorus_all su sv (notP_of_degree_four _ ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property))
      outside a hp (phosphorusEnumeration i a hp) false

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.twin_coordinate_match

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingSpatialTransport RingHydrogenCompletion
open LocalizedChemicalRing (Input)
open RingRawRenumbering (molecularRecord)
open HydrogenLeafParity
variable {i : Input}

/-- Arbitrary new coordinates for two identical terminal ligands on an otherwise
fixed complete graph preserve every request, including queries on the moving ligands. -/
theorem twin_motion_nondegenerate (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (closed : plan i.molecule = [])
    (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) (ne : u ≠ v)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (nw : HydrogenPairParity.volume (framePoints i w hw (i.certified.canonicalLigandAtom c)) 1 ≠ 0)
    (nx : HydrogenPairParity.volume (framePoints i x hx (i.certified.canonicalLigandAtom c)) 1 ≠ 0)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids := by
  obtain ⟨g,choice,matchFrames⟩ := twin_coordinate_match w x hw hx c u v ne records lu lv fixed nw nx
  exact LeafAllRequests.all_original_ids (atGeometry i w hw) x closed u v (supported_of_bond_row lu).degree_one
    (supported_of_bond_row lv).degree_one g.atoms choice (closed_placements g w x hx matchFrames closed closed) ids

/-- Equality of the coordinate gates suffices even when a full geometry is rejected. -/
theorem twin_motion_report (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (closed : plan i.molecule = [])
    (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) (ne : u ≠ v)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (gate : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) =
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx))
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids := by
  by_cases gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true
  · exact twin_motion_nondegenerate w x hw hx closed c u v ne records lu lv fixed
      (admitted_nonzero w hw c gw) (admitted_nonzero x hx c (gate ▸ gw)) ids
  · have off (z : SpatialConfiguration) (hz : z.positions.length = size i)
        (bad : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i z hz) ≠ true) :
        RingHydrogenReport.fromRaw? i.molecule z ids = none := by
      rw [RingHydrogenReport.fromRaw_closed_eq closed]
      cases got : RingChemicalReport.fromRaw? i.molecule z ids with
      | none => rfl
      | some rows => exact (bad ((closed_domain (atGeometry i z hz) closed ids).mp ⟨rows,got⟩).2).elim
    rw [off w hw gw,off x hx (gate ▸ gw)]
/-- The complete raw API distinguishes the two placements exactly when their global admission verdicts differ. -/
theorem twin_motion_iff (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (closed : plan i.molecule = [])
    (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) (ne : u ≠ v)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    : (∀ ids, RingHydrogenReport.fromRaw? i.molecule x ids = RingHydrogenReport.fromRaw? i.molecule w ids) ↔
      LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) =
        LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) := by
  constructor
  · intro reports
    have empty (z : SpatialConfiguration) (hz : z.positions.length = size i) :
        (∃ rows, RingHydrogenReport.fromRaw? i.molecule z [] = some rows) ↔
          LocalizedChemicalRing.coordinatesAdmitted (atGeometry i z hz) = true := by
      rw [RingHydrogenReport.fromRaw_closed_eq closed]
      simpa using closed_domain (atGeometry i z hz) closed []
    apply Bool.eq_iff_iff.mpr
    rw [←empty w hw,←empty x hx,reports []]
  · exact fun gate ids => twin_motion_report w x hw hx closed c u v ne records lu lv fixed gate ids
end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.twin_motion_report
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.twin_motion_iff
namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter OrdinaryHydrogenSpellings
open RingSpatialTransport RingNumberedHydrogenGeometry
open RingHydrogenCompletion RingPyramidalChoices
open RingRawRenumbering (molecularRecord)
open LocalizedChemicalRing (Input)
variable {i j : Input}

theorem indexed_admission (g : GraphMap i j) :
    LocalizedChemicalRing.coordinatesAdmitted (withSourceGeometry i j g.atoms) =
      LocalizedChemicalRing.coordinatesAdmitted i := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry.symm,
    RingRawRenumbering.AtomMap.coordinates g.atSourceGeometry⟩

/-- Two completed presentations may differ in numbering, inline H records and
both coordinates at an identical pair of terminal ligands. Admission is the only
geometric gate; the two written determinants may have opposite signs. -/
theorem closed_twin_spellings (g : GraphMap i j)
    (ci : plan i.molecule = []) (cj : plan j.molecule = [])
    (c : j.certified.TetrahedralCenter) (u v : j.certified.Atom) (ne : u ≠ v)
    (records : (j.molecule.atoms[u.val]?).map molecularRecord = (j.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : j.certified.Atom, j.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0)
    (lv : ∀ a : j.certified.Atom, j.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)
    (fixed : ∀ a : j.certified.Atom, a ≠ u → a ≠ v →
      (reindexed i j g.atoms).positions[a.val]? = j.spatial.positions[a.val]?)
    (gate : LocalizedChemicalRing.coordinatesAdmitted i = LocalizedChemicalRing.coordinatesAdmitted j)
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial (ids.map (moveId g.atoms)) =
      (RingHydrogenReport.fromRaw? i.molecule i.spatial ids).map (List.map fun row => (moveId g.atoms row.1,row.2)) := by
  rw [twin_motion_report (reindexed i j g.atoms) j.spatial (reindexed_full _) (full_original _) cj c u v ne
    records lu lv fixed (by rw [atGeometry_self]; exact (indexed_admission g).trans gate)]
  exact RingReportRenumber.closed_raw_report g.atSourceGeometry ci cj ids

variable {k : Nat} {coreAtom : Fin k → AtomSpec} {coreBond : Fin k → Fin k → Nat}

/-- Explicit, implicit and counted ordinary H at a single CH₂ can be compared
from the original inputs. The completion bijection is constructed from the
common retained graph and its per-parent H totals. -/
theorem prepared_twin_spelling {a b : Completion coreAtom coreBond} (s : PreparedSpelling a) (t : PreparedSpelling b)
    (counts : ∀ p, totalH a p = totalH b p)
    (single : sites s.source.molecule s.source.spatial s.result.molecule s.result.spatial = [])
    (single' : sites t.source.molecule t.source.spatial t.result.molecule t.result.spatial = [])
    (c : t.result.certified.TetrahedralCenter) (u v : t.result.certified.Atom) (ne : u ≠ v)
    (records : (t.result.molecule.atoms[u.val]?).map molecularRecord = (t.result.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ n : t.result.certified.Atom, t.result.molecule.bondOrder u.val n.val = if n = c.val then 1 else 0)
    (lv : ∀ n : t.result.certified.Atom, t.result.molecule.bondOrder v.val n.val = if n = c.val then 1 else 0)
    (fixed : ∀ n : t.result.certified.Atom, n ≠ u → n ≠ v →
      (reindexed s.result t.result (preparedMap s t counts).atoms).positions[n.val]? = t.result.spatial.positions[n.val]?)
    (gate : LocalizedChemicalRing.coordinatesAdmitted s.result = LocalizedChemicalRing.coordinatesAdmitted t.result)
    (parents : List (Fin k)) :
    RingHydrogenReport.fromRaw? t.source.molecule t.source.spatial (parents.map fun p => (b.core p).val) =
      (RingHydrogenReport.fromRaw? s.source.molecule s.source.spatial (parents.map fun p => (a.core p).val)).map
        (List.map fun row => (moveId (preparedMap s t counts).atoms row.1,row.2)) := by
  have bounds (z : Completion coreAtom coreBond) (p : PreparedSpelling z) :
      ∀ n ∈ parents.map (fun v => (z.core v).val), n < p.source.molecule.atomCount := by
    intro n hn
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hn
    rw [p.raw]; exact (z.core v).isLt
  rw [RingHydrogenReport.fromRaw_materialized_eq (readmit t.source) t.coordinates t.prepared single' _ (bounds b t),
      RingHydrogenReport.fromRaw_materialized_eq (readmit s.source) s.coordinates s.prepared single _ (bounds a s)]
  have result := closed_twin_spellings (preparedMap s t counts) (prepare?_closed s.prepared)
    (prepare?_closed t.prepared) c u v ne records lu lv fixed gate (parents.map fun p => (a.core p).val)
  simpa only [List.map_map,Function.comp_def,preparedMap_core] using result

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.prepared_twin_spelling

namespace TetraStereo.Engine.RingHydrogenSpelling
open OneCenter RingSpatialTransport RingNumberedHydrogenGeometry RingActiveDistanceSchedule
open RingActivePairs RingRawRenumbering HydrogenLeafParity
open LocalizedChemicalRing (Input)
variable {i : Input}

/-- One choice of identity or H exchange works simultaneously for every root,
batch and occurrence of the public chemical queue at both coordinate tables. -/
theorem twin_motion_stores (w x : SpatialConfiguration)
    (hw : w.positions.length = size i) (hx : x.positions.length = size i)
    (c : i.certified.TetrahedralCenter) (u v : i.certified.Atom) (ne : u ≠ v)
    (records : (i.molecule.atoms[u.val]?).map molecularRecord = (i.molecule.atoms[v.val]?).map molecularRecord)
    (lu : ∀ a : i.certified.Atom, i.molecule.bondOrder u.val a.val = if a = c.val then 1 else 0)
    (lv : ∀ a : i.certified.Atom, i.molecule.bondOrder v.val a.val = if a = c.val then 1 else 0)
    (fixed : ∀ a : i.certified.Atom, a ≠ u → a ≠ v → w.positions[a.val]? = x.positions[a.val]?)
    (gw : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i w hw) = true)
    (gx : LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x hx) = true) :
    ∃ g : GraphMap (atGeometry i w hw) (atGeometry i x hx),
      (g.atoms = Equiv.refl i.certified.Atom ∨ g.atoms = Equiv.swap u v) ∧
      ∀ root k, k ≤ height (atGeometry i w hw) + 1 → ∀ q,
        sphereEntry (atGeometry i w hw) root k q = sphereEntry (atGeometry i x hx) (g.atoms root) k
          ((reindexSite _ (reindexed _ _ g.atoms) (reindexed_full _)).symm
            (AtomMap.site g.atSourceGeometry q)) := by
  obtain ⟨g,choice,_,hands⟩ := twin_coordinate_match w x hw hx c u v ne records lu lv fixed
    (admitted_nonzero w hw c gw) (admitted_nonzero x hx c gx)
  exact ⟨g.atTables w x hw hx, choice, graph_sphereEntry (g.atTables w x hw hx) gw hands⟩

end TetraStereo.Engine.RingHydrogenSpelling
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.twin_motion_stores
