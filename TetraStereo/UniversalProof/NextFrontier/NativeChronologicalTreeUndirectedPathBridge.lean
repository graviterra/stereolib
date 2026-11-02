import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.OneCenter.ChronologicalPhysicalTree
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedRealPaths

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalTreeUndirectedPathBridge
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeGeneratedRealPaths

/-- Actual undirected adjacency to a larger atom selects the forward raw edge, by chronology. -/
theorem physical_edge_to_larger {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {small large : Nat} (ordered : small < large) (adjacent : 0 < mol.bondOrder small large) :
    ∃ bond ∈ mol.bonds, bond.source = small ∧ bond.target = large := by
  obtain ⟨bond, member, connected⟩ :=
    (RawMolecule.bondOrder_pos_iff_exists_bond mol (ne_of_lt ordered)).mp adjacent
  have chronological := (tree.2.1 bond member).2.1
  simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connected
  rcases connected with ⟨source, target⟩ | ⟨source, target⟩
  · exact ⟨bond, member, source, target⟩
  · rw [source, target] at chronological
    omega

/-- A vertex has at most one smaller physical neighbor, derived from raw target inventory. -/
theorem smaller_physical_neighbors_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {peak first second : Nat}
    (firstSmall : first < peak) (secondSmall : second < peak)
    (firstEdge : 0 < mol.bondOrder peak first) (secondEdge : 0 < mol.bondOrder peak second) :
    first = second := by
  have firstPositive : 0 < mol.bondOrder first peak := by
    rwa [mol.bondOrder_symm first peak]
  have secondPositive : 0 < mol.bondOrder second peak := by
    rwa [mol.bondOrder_symm second peak]
  obtain ⟨a, ha, asource, atarget⟩ := physical_edge_to_larger tree firstSmall firstPositive
  obtain ⟨b, hb, bsource, btarget⟩ := physical_edge_to_larger tree secondSmall secondPositive
  have same : a = b := List.inj_on_of_nodup_map tree.2.2.1 ha hb (atarget.trans btarget.symm)
  exact asource.symm.trans ((congrArg RawBond.source same).trans bsource)

/-- Three actual consecutive physical vertices cannot form a distinct-neighbor strict peak. -/
theorem three_vertex_peak_excluded {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {first peak last : Nat} (path : RawBondedPath mol [first, peak, last])
    (firstSmall : first < peak) (lastSmall : last < peak) (different : first ≠ last) : False := by
  have edges : 0 < mol.bondOrder first peak ∧ 0 < mol.bondOrder peak last := by
    simpa only [RawBondedPath, List.isChain_cons_cons, List.isChain_singleton, and_true] using path
  have firstEdge : 0 < mol.bondOrder peak first := by
    rw [mol.bondOrder_symm peak first]
    exact edges.1
  exact different (smaller_physical_neighbors_unique tree firstSmall lastSmall firstEdge edges.2)

/-- The no-peak cut applies to every interior triple of an arbitrary actual supported simple path. -/
theorem simple_path_interior_peak_excluded {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (before after : List Nat) (first peak last : Nat)
    (simple : (before ++ first :: peak :: last :: after).Nodup)
    (path : RawBondedPath mol (before ++ first :: peak :: last :: after))
    (firstSmall : first < peak) (lastSmall : last < peak) : False := by
  have suffix : (first :: peak :: last :: after).IsChain (fun a b => 0 < mol.bondOrder a b) :=
    List.IsChain.right_of_append path
  have firstEdge := (List.isChain_cons_cons.mp suffix).1
  have lastEdge := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp suffix).2).1
  have firstPositive : 0 < mol.bondOrder peak first := by
    rwa [mol.bondOrder_symm peak first]
  have same := smaller_physical_neighbors_unique tree firstSmall lastSmall firstPositive lastEdge
  have suffixSimple := (List.nodup_append.mp simple).2.1
  have fresh := (List.nodup_cons.mp suffixSimple).1
  apply fresh
  rw [same]
  exact List.mem_cons_of_mem peak (List.mem_cons_self)

/-- A vertex that bounds every path atom cannot occur strictly inside a supported simple path. -/
theorem supported_path_maximum_not_interior {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (before after : List Nat) (first peak last : Nat)
    (simple : (before ++ first :: peak :: last :: after).Nodup)
    (path : RawBondedPath mol (before ++ first :: peak :: last :: after))
    (maximal : ∀ atom ∈ before ++ first :: peak :: last :: after, atom ≤ peak) : False := by
  have suffixSimple := (List.nodup_append.mp simple).2.1
  have firstFresh := (List.nodup_cons.mp suffixSimple).1
  have peakFresh := (List.nodup_cons.mp (List.nodup_cons.mp suffixSimple).2).1
  have firstNe : first ≠ peak := by
    intro same
    apply firstFresh
    rw [same]
    exact List.mem_cons_self
  have lastNe : last ≠ peak := by
    intro same
    apply peakFresh
    rw [← same]
    exact List.mem_cons_self
  have firstBound := maximal first (List.mem_append_right _ (List.mem_cons_self))
  have lastBound := maximal last
    (List.mem_append_right _ (List.mem_cons_of_mem first (List.mem_cons_of_mem peak (List.mem_cons_self))))
  exact simple_path_interior_peak_excluded tree before after first peak last
    simple path (lt_of_le_of_ne firstBound firstNe) (lt_of_le_of_ne lastBound lastNe)

/-- The same raw-degree argument excludes a closed polygon whose chosen maximal vertex has
    distinct first/last interior neighbors. This is a cycle cut, not a global IsAcyclic claim. -/
theorem closed_peak_polygon_excluded {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (peak first last : Nat) (middle : List Nat)
    (path : RawBondedPath mol (peak :: first :: (middle ++ [last, peak])))
    (firstSmall : first < peak) (lastSmall : last < peak) (different : first ≠ last) : False := by
  have firstEdge := (List.isChain_cons_cons.mp path).1
  have rearranged : (peak :: first :: middle ++ [last, peak]).IsChain
      (fun a b => 0 < mol.bondOrder a b) := by
    simpa only [List.cons_append] using path
  have lastEdge := (List.isChain_append_cons_cons.mp rearranged).2.1
  have lastPositive : 0 < mol.bondOrder peak last := by
    rwa [mol.bondOrder_symm peak last]
  exact different (smaller_physical_neighbors_unique tree firstSmall lastSmall firstEdge lastPositive)

end TetraStereo.UniversalProof.NativeChronologicalTreeUndirectedPathBridge
