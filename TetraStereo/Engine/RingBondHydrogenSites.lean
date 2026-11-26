import TetraStereo.Engine.RingBondHydrogenPreparation
import TetraStereo.Engine.RingPyramidalChoiceSwap

/-! Bond-record reordering preserves the actual omitted-hydrogen sites up to
reversing their two retained neighbors, hence preserves the whole placement family. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBondHydrogenSites
open OneCenter RingHydrogenCompletion RingPyramidalChoices
open LocalizedChemicalRing (Input)
open RingBondRecordOrder (Presentation raw_atomCount writtenNeighbors_perm missing_eq addedParents_eq)

private def reversePresentation {i j : Input} (p : Presentation i j) : Presentation j i :=
  ⟨p.atoms.symm,p.bonds.symm,p.positions.symm⟩

private theorem pair_order {x y : Nat} {zs : List Nat} (apart : x ≠ y) (perm : [x,y].Perm zs) :
    zs = [x,y] ∨ zs = [y,x] := by
  have len : zs.length = 2 := by simpa using perm.length_eq.symm
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp len
  have hx : x = a ∨ x = b := by simpa using perm.mem_iff.mp (by simp : x ∈ [x,y])
  have hy : y = a ∨ y = b := by simpa using perm.mem_iff.mp (by simp : y ∈ [x,y])
  rcases hx with hxa | hxb <;> rcases hy with hya | hyb
  · exact False.elim (apart (hxa.trans hya.symm))
  · left; rw [hxa,hyb]
  · right; rw [hxb,hya]
  · exact False.elim (apart (hxb.trans hyb.symm))

/-- Fresh output rows are obtained from the completion certificate, not assumed
as site outcomes. Their planned parent is invariant under the source permutation. -/
private theorem fresh_row_transport {i j : Input} (p : Presentation i j)
    {out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (right : Certified j.molecule j.spatial out' pos') (positions : pos.positions = pos'.positions)
    {n h : Nat} (ge : i.molecule.atomCount ≤ h) (bound : h < pos.positions.length)
    (parent : (addedParents i.molecule)[h-i.molecule.atomCount]? = some n) :
    out'.writtenNeighbors h = [n] := by
  have ge' : j.molecule.atomCount ≤ h := by rw [← raw_atomCount p]; exact ge
  have lt' : h < out'.atomCount := by rw [← right.positions_length,← positions]; exact bound
  obtain ⟨q,hq,row⟩ := right.fresh_row ge' lt'
  rw [← addedParents_eq p,← raw_atomCount p] at hq
  have same : q = n := Option.some.inj (hq.symm.trans parent)
  simpa only [same] using row

private theorem valid_same {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (right : Certified j.molecule j.spatial out' pos') (positions : pos.positions = pos'.positions)
    {n : Nat} {s : Site} (v : Valid i.molecule i.spatial out pos n s)
    (row : j.molecule.writtenNeighbors n = [s.first,s.second]) :
    Valid j.molecule j.spatial out' pos' n s := by
  obtain ⟨par,active,miss,_,apart,center,first,second,ge,parent,_,bound,normal,np,fp,sp⟩ := v
  refine ⟨par,?_,?_,row,apart,?_,?_,?_,?_,?_,?_,?_,normal,?_,?_,?_⟩
  · rw [← p.atoms]; exact active
  · rw [← missing_eq p]; exact miss
  · rw [← p.positions]; exact center
  · rw [← p.positions]; exact first
  · rw [← p.positions]; exact second
  · rw [← raw_atomCount p]; exact ge
  · rw [← addedParents_eq p,← raw_atomCount p]; exact parent
  · exact fresh_row_transport p right positions ge bound parent
  · rw [← positions]; exact bound
  · rw [← raw_atomCount p]; exact np
  · rw [← raw_atomCount p]; exact fp
  · rw [← raw_atomCount p]; exact sp

private theorem valid_flip {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (right : Certified j.molecule j.spatial out' pos') (positions : pos.positions = pos'.positions)
    {n : Nat} {s : Site} (v : Valid i.molecule i.spatial out pos n s)
    (row : j.molecule.writtenNeighbors n = [s.second,s.first]) :
    Valid j.molecule j.spatial out' pos' n s.flip := by
  obtain ⟨par,active,miss,_,apart,center,first,second,ge,parent,_,bound,normal,np,fp,sp⟩ := v
  refine ⟨par,?_,?_,row,apart.symm,?_,?_,?_,?_,?_,?_,?_,(Site.flip_normal_nonzero s).mpr normal,?_,?_,?_⟩
  · rw [← p.atoms]; exact active
  · rw [← missing_eq p]; exact miss
  · rw [← p.positions]; exact center
  · rw [← p.positions]; exact second
  · rw [← p.positions]; exact first
  · rw [← raw_atomCount p]; exact ge
  · rw [← addedParents_eq p,← raw_atomCount p]; exact parent
  · exact fresh_row_transport p right positions ge bound parent
  · rw [← positions]; exact bound
  · rw [← raw_atomCount p]; exact np
  · rw [← raw_atomCount p]; exact sp
  · rw [← raw_atomCount p]; exact fp

private theorem draft_same {i j : Input} (p : Presentation i j) (n : Nat)
    (row : j.molecule.writtenNeighbors n = i.molecule.writtenNeighbors n) :
    draft? j.molecule j.spatial n = draft? i.molecule i.spatial n := by
  simp only [draft?,row,← addedParents_eq p,← raw_atomCount p,← p.positions]

private theorem draft_flip {i j : Input} (p : Presentation i j) (n x y : Nat)
    (leftRow : i.molecule.writtenNeighbors n = [x,y])
    (rightRow : j.molecule.writtenNeighbors n = [y,x]) :
    draft? j.molecule j.spatial n = (draft? i.molecule i.spatial n).map Site.flip := by
  simp only [draft?,leftRow,rightRow,← addedParents_eq p,← raw_atomCount p,← p.positions]
  cases ho : offset? (addedParents i.molecule) n <;>
    cases hc : i.spatial.positions[n]? <;>
    cases hx : i.spatial.positions[x]? <;>
    cases hy : i.spatial.positions[y]? <;> simp_all [Site.flip]

private theorem draft_of_site {m out : RawMolecule} {g pos : SpatialConfiguration} {n : Nat} {s : Site}
    (hit : site? m g out pos n = some s) : draft? m g n = some s := by
  unfold site? at hit
  split at hit <;> try contradiction
  obtain ⟨d,hd,admitted⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨same,_⟩ := admit_eq_some admitted
  simpa only [← same] using hd

private theorem site_of_draft {m out : RawMolecule} {g pos : SpatialConfiguration} {n : Nat} {s : Site}
    (v : Valid m g out pos n s) (draft : draft? m g n = some s) : site? m g out pos n = some s := by
  simp [site?,v.2.1,draft,admit,v]

private theorem site_forward {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (right : Certified j.molecule j.spatial out' pos') (positions : pos.positions = pos'.positions)
    {n : Nat} {s : Site} (hit : site? i.molecule i.spatial out pos n = some s) :
    ∃ t, site? j.molecule j.spatial out' pos' n = some t ∧ (t = s ∨ t = s.flip) := by
  have v := site?_valid hit
  have original := v
  obtain ⟨_,_,_,row,apart,_,_,_,_,_,_,_,_,np,_,_⟩ := v
  have perm := writtenNeighbors_perm p n np
  rw [row] at perm
  rcases pair_order apart perm with same | flipped
  · refine ⟨s,site_of_draft (valid_same p right positions original same) ?_,Or.inl rfl⟩
    rw [draft_same p n (same.trans row.symm)]
    exact draft_of_site hit
  · refine ⟨s.flip,site_of_draft (valid_flip p right positions original flipped) ?_,Or.inr rfl⟩
    rw [draft_flip p n s.first s.second row flipped,draft_of_site hit]
    rfl

/-- Site admission itself is invariant, with only the written orientation of
its two retained neighbors allowed to reverse. No placement outcome is assumed. -/
theorem site_related {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (left : Certified i.molecule i.spatial out pos) (right : Certified j.molecule j.spatial out' pos')
    (positions : pos.positions = pos'.positions) (n : Nat) :
    Option.Rel (fun a b => b = a ∨ b = a.flip)
      (site? i.molecule i.spatial out pos n) (site? j.molecule j.spatial out' pos' n) := by
  cases hs : site? i.molecule i.spatial out pos n with
  | some s =>
    obtain ⟨t,ht,related⟩ := site_forward p right positions hs
    rw [ht]
    exact .some related
  | none =>
    cases ht : site? j.molecule j.spatial out' pos' n with
    | none => exact .none
    | some t =>
      obtain ⟨s,h, _⟩ := site_forward (reversePresentation p) left positions.symm ht
      rw [hs] at h
      contradiction

/-- Both actual lists follow the same ascending parent inventory. Each
corresponding site is identical or exchanges its first/second retained ray. -/
theorem sites_related {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (left : Certified i.molecule i.spatial out pos) (right : Certified j.molecule j.spatial out' pos')
    (positions : pos.positions = pos'.positions) :
    List.Forall₂ (fun a b => b = a ∨ b = a.flip)
      (sites i.molecule i.spatial out pos) (sites j.molecule j.spatial out' pos') := by
  unfold sites
  rw [← raw_atomCount p]
  refine List.rel_filterMap (R := fun a b : Nat => a = b) ?_ ?_
  · intro a b h
    subst b
    exact site_related p left right positions a
  · exact List.forall₂_same.mpr (fun _ _ => rfl)

/-- The complete orientation-choice families agree up to a permutation, even
when any number of written two-neighbor frames are reversed independently. -/
theorem choices_perm {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (left : Certified i.molecule i.spatial out pos) (right : Certified j.molecule j.spatial out' pos')
    (positions : pos.positions = pos'.positions) :
    (choices (sites i.molecule i.spatial out pos) pos.positions).Perm
      (choices (sites j.molecule j.spatial out' pos') pos'.positions) := by
  rw [← positions]
  exact choices_perm_of_related (sites_related p left right positions) _

theorem variants_perm {i j : Input} (p : Presentation i j)
    {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (left : Certified i.molecule i.spatial out pos) (right : Certified j.molecule j.spatial out' pos')
    (positions : pos.positions = pos'.positions) :
    (variants i.molecule i.spatial out pos).Perm (variants j.molecule j.spatial out' pos') := by
  exact (choices_perm p left right positions).map (fun ps => ({positions := ps} : SpatialConfiguration))

end TetraStereo.Engine.RingBondHydrogenSites
assert_kernel_only TetraStereo.Engine.RingBondHydrogenSites.site_related
assert_kernel_only TetraStereo.Engine.RingBondHydrogenSites.sites_related
assert_kernel_only TetraStereo.Engine.RingBondHydrogenSites.choices_perm
assert_kernel_only TetraStereo.Engine.RingBondHydrogenSites.variants_perm
