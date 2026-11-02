import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Physical terminal twins under molecular automorphisms

The twin predicate is purely constitutional. An automorphism transports the actual terminal
neighbors, their labels and their bonds, so the predicate holds at the image center exactly when
it holds at the source. No acyclicity, configuration sign or descriptor hypothesis is needed.
This supplies the twin case of the cyclic generated-reader transport.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport

open CertifiedLocalizedCIPInput

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem neighbor_singleton_transport {graph : MoleculeGraph V} (e : graph.Aut)
    {a c : V} (neighbors : graph.neighborFinset a = {c}) :
    graph.neighborFinset ((e : Equiv.Perm V) a) = {(e : Equiv.Perm V) c} := by
  ext x
  obtain ⟨y, rfl⟩ := (e : Equiv.Perm V).surjective x
  simpa only [MoleculeGraph.mem_neighborFinset, Finset.mem_singleton,
    MoleculeGraph.Aut.adj_iff, Equiv.apply_eq_iff_eq] using
    (Finset.ext_iff.mp neighbors y)

theorem terminalTwinPair_transport {m : MultiCenterMolecule V} (e : m.Aut)
    {c : m.Center} {a b : V}
    (twins : TerminalTwinConfigurationGauge.TerminalTwinPair m c a b) :
    TerminalTwinConfigurationGauge.TerminalTwinPair m (m.centerPerm e c)
      ((e : Equiv.Perm V) a) ((e : Equiv.Perm V) b) := by
  let graphAut : m.mol.Aut := ⟨e.1, e.2.1⟩
  refine
    { ne := fun equal => twins.ne ((e : Equiv.Perm V).injective equal)
      neighbor_a := ?_
      neighbor_b := ?_
      z_eq := ?_
      mass_eq := ?_
      charge_eq := ?_
      bond_eq := ?_ }
  · exact neighbor_singleton_transport graphAut twins.neighbor_a
  · exact neighbor_singleton_transport graphAut twins.neighbor_b
  · exact (e.2.1.1 a).trans (twins.z_eq.trans (e.2.1.1 b).symm)
  · exact (e.2.1.2.1 a).trans (twins.mass_eq.trans (e.2.1.2.1 b).symm)
  · exact (e.2.1.2.2.1 a).trans (twins.charge_eq.trans (e.2.1.2.2.1 b).symm)
  · exact (e.2.1.2.2.2 c.1 a).trans
      (twins.bond_eq.trans (e.2.1.2.2.2 c.1 b).symm)

theorem actualPhysicalTerminalTwinCenter_transport
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    (e : m.Aut) {c : m.Center}
    (twins : ActualPhysicalTerminalTwinCenter input m c) :
    ActualPhysicalTerminalTwinCenter input m (m.centerPerm e c) := by
  obtain ⟨a, b, pair⟩ := twins
  exact ⟨(e : Equiv.Perm input.Atom) a, (e : Equiv.Perm input.Atom) b,
    terminalTwinPair_transport e pair⟩

theorem actualPhysicalTerminalTwinCenter_transport_iff
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    (e : m.Aut) (c : m.Center) :
    ActualPhysicalTerminalTwinCenter input m (m.centerPerm e c) ↔
      ActualPhysicalTerminalTwinCenter input m c := by
  constructor
  · intro twins
    have inverse : m.centerPerm (e⁻¹) (m.centerPerm e c) = c := by
      apply Subtype.ext
      simp [MultiCenterMolecule.centerPerm]
    have source := actualPhysicalTerminalTwinCenter_transport (e⁻¹) twins
    rwa [inverse] at source
  · exact actualPhysicalTerminalTwinCenter_transport e

end TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport.neighbor_singleton_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport.terminalTwinPair_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport_iff
