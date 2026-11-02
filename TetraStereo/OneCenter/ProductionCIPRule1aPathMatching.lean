import TetraStereo.OneCenter.ProductionCIPRule1aMatchingRealization

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

namespace RawMolecule

/-!
# Maximum matchings of an explicitly ordered path

These lemmas are independent of the molecular cycle detector.  They give the closed maximum-size
and maximum-family count of a path edge list without enumerating a particular molecule.  The cycle
fast path uses them after its exact-component certificate identifies the localized component with
one simple cycle.
-/

/-- Consecutive undirected edges of a vertex list, in list order. -/
def orderedPathEdges : List ℕ → List (ℕ × ℕ)
  | [] | [_] => []
  | first :: second :: rest => (first, second) :: orderedPathEdges (second :: rest)

@[simp] theorem orderedPathEdges_nil : orderedPathEdges [] = [] := rfl
@[simp] theorem orderedPathEdges_singleton (a : ℕ) : orderedPathEdges [a] = [] := rfl
@[simp] theorem orderedPathEdges_cons_cons (a b : ℕ) (rest : List ℕ) :
    orderedPathEdges (a :: b :: rest) = (a, b) :: orderedPathEdges (b :: rest) := rfl

theorem orderedPathEdges_length : ∀ vertices : List ℕ,
    (orderedPathEdges vertices).length = vertices.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      rw [orderedPathEdges_cons_cons, List.length_cons,
        orderedPathEdges_length (b :: rest)]
      simp

theorem endpoints_mem_of_mem_orderedPathEdges : ∀ {vertices : List ℕ} {edge : ℕ × ℕ},
    edge ∈ orderedPathEdges vertices → edge.1 ∈ vertices ∧ edge.2 ∈ vertices
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: rest, edge, h => by
      simp only [orderedPathEdges_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have ih := endpoints_mem_of_mem_orderedPathEdges h
        exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- Removing all edges incident to the first path edge leaves the path two vertices later. -/
theorem orderedPathEdges_filter_first (a b : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: rest).Nodup) :
    (orderedPathEdges (b :: rest)).filter (fun edge =>
      edge.1 != a && edge.2 != a && edge.1 != b && edge.2 != b) =
      orderedPathEdges rest := by
  cases rest with
  | nil => rfl
  | cons c rest =>
      have haParts := List.nodup_cons.mp hnodup
      have hbParts := List.nodup_cons.mp haParts.2
      have hbc : b ≠ c := fun h => hbParts.1 (by simp [h])
      simp only [orderedPathEdges_cons_cons, List.filter_cons]
      rw [show (b != a && c != a && b != b && c != b) = false by simp]
      simp only [Bool.false_eq_true, if_false]
      apply List.filter_eq_self.2
      intro edge hedge
      have hendpoints := endpoints_mem_of_mem_orderedPathEdges hedge
      have hea : edge.1 ≠ a := fun h => haParts.1 (by simp [← h, hendpoints.1])
      have heb : edge.2 ≠ a := fun h => haParts.1 (by simp [← h, hendpoints.2])
      have hba : edge.1 ≠ b := fun h => hbParts.1 (by simp [← h, hendpoints.1])
      have hbb : edge.2 ≠ b := fun h => hbParts.1 (by simp [← h, hendpoints.2])
      simp [hea, heb, hba, hbb]

/-- Closed maximum selected-edge cardinality of a path on `vertexCount` vertices. -/
def pathMaximumSize (vertexCount : ℕ) : ℕ := vertexCount / 2

/-- Number of maximum matchings of a path on `vertexCount` vertices. -/
def pathMaximumCount (vertexCount : ℕ) : ℕ :=
  if vertexCount % 2 = 0 then 1 else vertexCount / 2 + 1

/-- Maximum-matching statistics of a path when the observed atom lies outside its vertices. -/
theorem exhaustiveMancudeMatchingStats_orderedPath_of_attached_not_mem
    (mol : RawMolecule) (attached : ℕ) : ∀ vertices : List ℕ,
    vertices.Nodup → attached ∉ vertices →
      mol.exhaustiveMancudeMatchingStats attached (orderedPathEdges vertices) =
        { size := pathMaximumSize vertices.length
          count := pathMaximumCount vertices.length
          partnerZSum := 0 }
  | [], _, _ => by
      rw [show orderedPathEdges [] = [] by rfl]
      rw [exhaustiveMancudeMatchingStats.eq_1]
      simp [pathMaximumSize, pathMaximumCount]
  | [a], _, _ => by
      rw [show orderedPathEdges [a] = [] by rfl]
      rw [exhaustiveMancudeMatchingStats.eq_1]
      simp [pathMaximumSize, pathMaximumCount]
  | a :: b :: rest, hnodup, hattached => by
      have hparts := List.nodup_cons.mp hnodup
      have hbparts := List.nodup_cons.mp hparts.2
      have htailNodup : rest.Nodup := hbparts.2
      have hattachedRest : attached ∉ rest := fun h => hattached (by simp [h])
      have hfilter := orderedPathEdges_filter_first a b rest hnodup
      rw [orderedPathEdges_cons_cons, exhaustiveMancudeMatchingStats.eq_2, hfilter,
        exhaustiveMancudeMatchingStats_orderedPath_of_attached_not_mem mol attached
          (b :: rest) hparts.2 (fun h => hattached (by simp [h])),
        exhaustiveMancudeMatchingStats_orderedPath_of_attached_not_mem mol attached
          rest htailNodup hattachedRest]
      have ha : a ≠ attached := fun h => hattached (by simp [h])
      have hb : b ≠ attached := fun h => hattached (by simp [h])
      have haBool : (a == attached) = false := by simp [ha]
      have hbBool : (b == attached) = false := by simp [hb]
      simp only [combineMancudeStats, haBool, hbBool]
      by_cases heven : rest.length % 2 = 0
      · have hlt : (rest.length + 1) / 2 < rest.length / 2 + 1 := by omega
        have htotal : (rest.length + 2) % 2 = 0 := by omega
        have hsize : (rest.length + 2) / 2 = rest.length / 2 + 1 := by omega
        simp [pathMaximumSize, pathMaximumCount, heven, hlt, htotal, hsize]
      · have hodd : rest.length % 2 = 1 := by omega
        have hevenSucc : (rest.length + 1) % 2 = 0 := by omega
        have heq : (rest.length + 1) / 2 = rest.length / 2 + 1 := by omega
        have htotal : (rest.length + 2) % 2 = 1 := by omega
        have hsize : (rest.length + 2) / 2 = rest.length / 2 + 1 := by omega
        simp [pathMaximumSize, pathMaximumCount, hodd, hevenSucc,
          heq, htotal, hsize]
        omega
termination_by vertices => vertices.length

/-- Number of maximum path matchings pairing the first vertex with its unique path neighbor. -/
def pathHeadPartnerMultiplicity (vertexCount : ℕ) : ℕ :=
  if vertexCount % 2 = 0 then 1 else vertexCount / 2

/-- Closed path statistics observed at the first vertex. -/
theorem exhaustiveMancudeMatchingStats_orderedPath_head
    (mol : RawMolecule) (a b : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: rest).Nodup) :
    mol.exhaustiveMancudeMatchingStats a (orderedPathEdges (a :: b :: rest)) =
      { size := pathMaximumSize (rest.length + 2)
        count := pathMaximumCount (rest.length + 2)
        partnerZSum := pathHeadPartnerMultiplicity (rest.length + 2) * mol.atomZAt b } := by
  have hparts := List.nodup_cons.mp hnodup
  have hbparts := List.nodup_cons.mp hparts.2
  have haTail : a ∉ b :: rest := hparts.1
  have haRest : a ∉ rest := fun h => hparts.1 (by simp [h])
  have hfilter := orderedPathEdges_filter_first a b rest hnodup
  rw [orderedPathEdges_cons_cons, exhaustiveMancudeMatchingStats.eq_2, hfilter,
    exhaustiveMancudeMatchingStats_orderedPath_of_attached_not_mem mol a
      (b :: rest) hparts.2 haTail,
    exhaustiveMancudeMatchingStats_orderedPath_of_attached_not_mem mol a
      rest hbparts.2 haRest]
  have hab : b ≠ a := by
    exact fun h => hparts.1 (by simp [h])
  have haa : (a == a) = true := by simp
  simp only [haa, if_true]
  by_cases heven : rest.length % 2 = 0
  · have hlt : (rest.length + 1) / 2 < rest.length / 2 + 1 := by omega
    have htotal : (rest.length + 2) % 2 = 0 := by omega
    have hsize : (rest.length + 2) / 2 = rest.length / 2 + 1 := by omega
    simp [combineMancudeStats, pathMaximumSize, pathMaximumCount,
      pathHeadPartnerMultiplicity, heven, hlt, htotal, hsize]
  · have hodd : rest.length % 2 = 1 := by omega
    have hevenSucc : (rest.length + 1) % 2 = 0 := by omega
    have heq : (rest.length + 1) / 2 = rest.length / 2 + 1 := by omega
    have htotal : (rest.length + 2) % 2 = 1 := by omega
    have hsize : (rest.length + 2) / 2 = rest.length / 2 + 1 := by omega
    simp [combineMancudeStats, pathMaximumSize, pathMaximumCount,
      pathHeadPartnerMultiplicity, hodd, hevenSucc, heq, htotal, hsize]
    omega

/-- Filtering the final vertex out of a path removes exactly its final edge. -/
theorem orderedPathEdges_filter_last (vertices : List ℕ) (z : ℕ)
    (hz : z ∉ vertices) :
    (orderedPathEdges (vertices ++ [z])).filter (fun edge =>
      edge.1 != z && edge.2 != z) = orderedPathEdges vertices := by
  induction vertices with
  | nil => rfl
  | cons a vertices ih =>
      cases vertices with
      | nil =>
          simp [orderedPathEdges]
      | cons b rest =>
          have haz : a ≠ z := fun h => hz (by simp [h])
          have hbz : b ≠ z := fun h => hz (by simp [h])
          have hzTail : z ∉ b :: rest := fun h => hz (by simp [h])
          simp only [List.cons_append, orderedPathEdges_cons_cons, List.filter_cons]
          rw [show (a != z && b != z) = true by simp [haz, hbz]]
          simp only [if_true]
          congr 1
          exact ih hzTail

/-- A cycle edge list ordered with its closing edge first. -/
def closingFirstCycleEdges (a : ℕ) (middle : List ℕ) (z : ℕ) :
    List (ℕ × ℕ) :=
  (a, z) :: orderedPathEdges (a :: (middle ++ [z]))

/-- Including the first closing edge removes the two incident path edges and leaves the middle
path. -/
theorem closingFirstCycleEdges_filter_closing (a b : ℕ) (rest : List ℕ) (z : ℕ)
    (hnodup : (a :: b :: (rest ++ [z])).Nodup) :
    (orderedPathEdges (a :: b :: (rest ++ [z]))).filter (fun edge =>
      edge.1 != a && edge.2 != a && edge.1 != z && edge.2 != z) =
      orderedPathEdges (b :: rest) := by
  have hparts := List.nodup_cons.mp hnodup
  have hbparts := List.nodup_cons.mp hparts.2
  have hab : a ≠ b := fun h => hparts.1 (by simp [h])
  simp only [orderedPathEdges_cons_cons, List.filter_cons]
  rw [show (a != a && b != a && a != z && b != z) = false by simp]
  simp only [Bool.false_eq_true, if_false]
  have haTail : a ∉ b :: (rest ++ [z]) := hparts.1
  have hfilterA :
      (orderedPathEdges (b :: (rest ++ [z]))).filter (fun edge =>
        edge.1 != a && edge.2 != a) = orderedPathEdges (b :: (rest ++ [z])) := by
    apply List.filter_eq_self.2
    intro edge hedge
    have hendpoints := endpoints_mem_of_mem_orderedPathEdges hedge
    have hleft : edge.1 ≠ a := fun h => haTail (by simpa [h] using hendpoints.1)
    have hright : edge.2 ≠ a := fun h => haTail (by simpa [h] using hendpoints.2)
    simp [hleft, hright]
  have hz : z ∉ b :: rest := by
    have hzAll := (List.nodup_append.1 hbparts.2).2.2
    intro h
    simp only [List.mem_cons] at h
    rcases h with hzb | hrest
    · exact hbparts.1 (by simp [hzb])
    · exact (hzAll z hrest z (by simp)) rfl
  calc
    (orderedPathEdges (b :: (rest ++ [z]))).filter (fun edge =>
        edge.1 != a && edge.2 != a && edge.1 != z && edge.2 != z) =
        ((orderedPathEdges (b :: (rest ++ [z]))).filter (fun edge =>
          edge.1 != a && edge.2 != a)).filter (fun edge =>
            edge.1 != z && edge.2 != z) := by
          rw [List.filter_filter]
          congr 2
          funext edge
          simp only [Bool.and_comm, Bool.and_left_comm]
    _ = (orderedPathEdges (b :: (rest ++ [z]))).filter (fun edge =>
          edge.1 != z && edge.2 != z) := by rw [hfilterA]
    _ = orderedPathEdges (b :: rest) :=
      orderedPathEdges_filter_last (b :: rest) z hz

/-- Closed maximum-matching statistics of a simple cycle, with arbitrary atomic-number labels at
the two neighbors of the observed vertex. -/
theorem exhaustiveMancudeMatchingStats_closingFirstCycle
    (mol : RawMolecule) (a b z : ℕ) (rest : List ℕ)
    (hnodup : (a :: b :: (rest ++ [z])).Nodup) :
    mol.exhaustiveMancudeMatchingStats a
        (closingFirstCycleEdges a (b :: rest) z) =
      if (rest.length + 3) % 2 = 0 then
        { size := (rest.length + 3) / 2
          count := 2
          partnerZSum := mol.atomZAt b + mol.atomZAt z }
      else
        { size := (rest.length + 3) / 2
          count := rest.length + 3
          partnerZSum := ((rest.length + 3) / 2) *
            (mol.atomZAt b + mol.atomZAt z) } := by
  have hparts := List.nodup_cons.mp hnodup
  have hbparts := List.nodup_cons.mp hparts.2
  have haMiddle : a ∉ b :: rest := by
    intro ha
    apply hparts.1
    simp only [List.mem_cons, List.mem_append]
    simp only [List.mem_cons] at ha
    rcases ha with hab | harest
    · exact Or.inl hab
    · exact Or.inr (Or.inl harest)
  have hmiddleNodup : (b :: rest).Nodup := by
    exact (List.nodup_append.1 hparts.2).1
  have hfilter := closingFirstCycleEdges_filter_closing a b rest z hnodup
  have hfilter' :
      (orderedPathEdges (a :: ((b :: rest) ++ [z]))).filter (fun edge =>
        edge.1 != a && edge.2 != a && edge.1 != z && edge.2 != z) =
        orderedPathEdges (b :: rest) := by
    simpa only [List.cons_append] using hfilter
  have hhead :
      mol.exhaustiveMancudeMatchingStats a
          (orderedPathEdges (a :: ((b :: rest) ++ [z]))) =
        { size := pathMaximumSize (rest.length + 3)
          count := pathMaximumCount (rest.length + 3)
          partnerZSum := pathHeadPartnerMultiplicity (rest.length + 3) * mol.atomZAt b } := by
    simpa only [List.cons_append, List.length_append, List.length_singleton] using
      exhaustiveMancudeMatchingStats_orderedPath_head mol a b (rest ++ [z]) hnodup
  unfold closingFirstCycleEdges
  rw [exhaustiveMancudeMatchingStats.eq_2]
  rw [hfilter',
    hhead,
    exhaustiveMancudeMatchingStats_orderedPath_of_attached_not_mem mol a
      (b :: rest) hmiddleNodup haMiddle]
  have haa : (a == a) = true := by simp
  simp only [haa, if_true]
  by_cases heven : (rest.length + 3) % 2 = 0
  · have hrestEven : rest.length % 2 = 1 := by omega
    have hmiddleEven : (rest.length + 1) % 2 = 0 := by omega
    have hsizes :
        (rest.length + 3) / 2 = (rest.length + 1) / 2 + 1 := by omega
    simp [combineMancudeStats, pathMaximumSize, pathMaximumCount,
      pathHeadPartnerMultiplicity, heven, hmiddleEven, hsizes]
  · have hodd : (rest.length + 3) % 2 = 1 := by omega
    have hmiddleOdd : (rest.length + 1) % 2 = 1 := by omega
    have hsizes :
        (rest.length + 3) / 2 = (rest.length + 1) / 2 + 1 := by omega
    simp [combineMancudeStats, pathMaximumSize, pathMaximumCount,
      pathHeadPartnerMultiplicity, hodd, hmiddleOdd, hsizes, Nat.mul_add]
    omega

end RawMolecule

end OneCenter
end TetraStereo
