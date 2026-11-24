import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation

namespace Figure14Parity

open TetraStereo.OneCenter CartesianPoint3 RationalTetrahedralPermutation

/-- A common reordering at both ends of a cage preserves the product of their signed
volumes. Permuting the three matched bridges and fixing the exocyclic bond is one case. -/
theorem commonReordering (a b c h d e f k : CartesianPoint3) (p : Equiv.Perm (Fin 4)) :
    permutedOrientedVolume a b c h p * permutedOrientedVolume d e f k p =
      orientedVolume a b c h * orientedVolume d e f k := by
  rw [permutedOrientedVolume_eq_if_permutationIsEven, permutedOrientedVolume_eq_if_permutationIsEven]
  split <;> simp

/-- For two parallel bridge triangles with the same three planar coordinates, the signed
volume product factors into a square and the two signed distances in the z direction. -/
theorem parallelFaces (ax ay bx by' cx cy top bottom : ℚ) (h k : CartesianPoint3) :
    orientedVolume ⟨ax, ay, top⟩ ⟨bx, by', top⟩ ⟨cx, cy, top⟩ h *
    orientedVolume ⟨ax, ay, bottom⟩ ⟨bx, by', bottom⟩ ⟨cx, cy, bottom⟩ k =
      ((bx - ax) * (cy - ay) - (by' - ay) * (cx - ax)) ^ 2 *
      (top - h.z) * (bottom - k.z) := by
  simp only [orientedVolume]
  ring

/-- With only two nonzero local hand signs as input, invariance under a simultaneous
bridge transposition leaves at most two distinguishable cases. -/
theorem twoHandClassification {α : Type*} (read : Bool → Bool → α)
    (invariant : ∀ a b, read (!a) (!b) = read a b) (a b : Bool) :
    read a b = if a == b then read false false else read false true := by
  cases a <;> cases b <;> simp
  · exact invariant false true
  · exact invariant false false

end Figure14Parity
