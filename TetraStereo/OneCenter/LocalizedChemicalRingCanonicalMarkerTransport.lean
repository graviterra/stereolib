import TetraStereo.OneCenter.DeclarativeCIPRetainedRelabelTransport
import TetraStereo.OneCenter.DeclarativeCIPPromotedCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The independent promotion marker depends on subtree priority and reference membership,
not the names of atoms. Its covariance uses rooted graph relabelling, so it applies when a
molecular symmetry moves the reference atom as well as the ligand. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCanonicalMarkerTransport

open DeclarativeCIP DeclarativeCIP.PromotedCanonical
open Certificate.CanonicalSphereKey

variable {Atom P : Type} [Fintype Atom] [DecidableEq Atom] [LinearOrder P]
  {left right : RootedDigraph Atom} {e : Equiv.Perm Atom}

theorem key_relabel (rel : RootedDigraph.Relabel e left right)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (markL : left.Node → Nat) (markR : right.Node → Nat)
    (priorEq : ∀ node, priorR (rel.toEquiv node) = priorL node)
    (markEq : ∀ node, markR (rel.toEquiv node) = markL node) (W D : Nat) :
    ∀ node, key right priorR markR W D (rel.toEquiv node) = key left priorL markL W D node := by
  refine node_induction left ?_
  intro node ih
  have children : rankedKeys right priorR markR W D (rel.toEquiv node) =
      rankedKeys left priorL markL W D node := by
    unfold rankedKeys
    rw [sortDesc_eq_of_perm
      ((childList_relabel_perm rel node).map (key right priorR markR W D)), List.map_map]
    congr 1
    exact List.map_congr_left fun child member => ih child ((left.mem_childList).1 member)
  rw [key_eq, key_eq, children, priorEq, markEq]

theorem markerKey_relabel (rel : RootedDigraph.Relabel e left right)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (markL : left.Node → Nat) (markR : right.Node → Nat)
    (priorEq : ∀ node, priorR (rel.toEquiv node) = priorL node)
    (markEq : ∀ node, markR (rel.toEquiv node) = markL node) (W D : Nat) (node : left.Node) :
    markerKey right priorR markR W D (rel.toEquiv node) =
      markerKey left priorL markL W D node := by
  unfold markerKey
  rw [key_relabel rel priorL priorR markL markR priorEq markEq]

end TetraStereo.OneCenter.LocalizedChemicalRingCanonicalMarkerTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCanonicalMarkerTransport.key_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCanonicalMarkerTransport.markerKey_relabel
