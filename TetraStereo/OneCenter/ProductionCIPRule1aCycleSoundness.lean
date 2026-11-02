import TetraStereo.OneCenter.ProductionCIPRule1aCycleRealization
import TetraStereo.OneCenter.ProductionCIPRule1aGlobalIntegration

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

private theorem cycle_alternate_lt
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount) (alternate : ℕ) (rest : List ℕ)
    (hexact : mol.SimpleCycleExactComponent attached.val
      (attached.val :: duplicated.val :: (rest ++ [alternate]))) :
    alternate < mol.atomCount := by
  let cycle := attached.val :: duplicated.val :: (rest ++ [alternate])
  let actual := mol.localizedMancudeComponentEdges attached.val
  have hcycle : containsUndirectedEdge (cycleEdges cycle) alternate attached.val = true := by
    rw [cycleEdges_eq_orderedPathEdges_append_closing]
    simp [containsUndirectedEdge]
  have hactual : containsUndirectedEdge actual alternate attached.val = true :=
    (hexact.edge_mem_iff alternate attached.val).1 hcycle
  have hrealizes := mol.localizedMancudeComponentEdges_realization
    hwellFormed hunique attached
  simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hactual
  rcases hactual with ⟨edge, hedge, hforward | hreverse⟩
  · have hbounds := hrealizes.endpointsInBounds edge hedge
    simpa [hforward.1] using hbounds.1
  · have hbounds := hrealizes.endpointsInBounds edge hedge
    simpa [hreverse.2] using hbounds.2

/-- The closed parity formula selected by a successful detector is exactly the independent average
over every maximum matching.  No bounded exhaustive result, assumed profile, or final-value
comparison appears in the statement or proof. -/
theorem simpleMancudeCycleLabel_exactAverage
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount) (cycle : List ℕ) (alternate : ℕ)
    (hcycle : mol.simpleMancudeCycle? attached.val duplicated.val =
      some (cycle, alternate)) :
    (mol.simpleMancudeCycleLabel duplicated.val alternate cycle).toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  classical
  have hcertificate := mol.simpleMancudeCycle?_certificate attached.val duplicated.val
    cycle alternate hcycle
  rcases hcertificate.shape with ⟨rest, hshape⟩
  subst cycle
  let alternateFin : Fin mol.atomCount :=
    ⟨alternate, mol.cycle_alternate_lt hwellFormed hunique attached duplicated alternate rest
      hcertificate.exactComponent⟩
  let edges := closingFirstCycleEdges attached.val (duplicated.val :: rest) alternate
  have hrealizes : LocalizedMancudeEdgeListRealization mol attached edges :=
    mol.closingFirstCycleEdges_realization hwellFormed hunique attached duplicated
      alternateFin rest hcertificate.exactComponent hcertificate.nodup
  have hstats := mol.exhaustiveMancudeMatchingStats_closingFirstCycle
    attached.val duplicated.val alternate rest hcertificate.nodup
  have hcount := mol.exhaustiveMancudeMatchingStats_count_eq_independent_card
    attached edges hrealizes
  have hsum := mol.exhaustiveMancudeMatchingStats_partnerZSum_eq_independent_sum
    attached edges hrealizes
  have hlength : (attached.val :: duplicated.val :: (rest ++ [alternate])).length =
      rest.length + 3 := by simp
  have hduplicatedZ : mol.atomZAt duplicated.val = mol.toMoleculeGraph.atomZ duplicated :=
    mol.atomZAt_eq_toMoleculeGraph_atomZ duplicated.val duplicated.isLt
  have halternateZ : mol.atomZAt alternate = mol.toMoleculeGraph.atomZ alternateFin :=
    mol.atomZAt_eq_toMoleculeGraph_atomZ alternate alternateFin.isLt
  by_cases heven : (rest.length + 3) % 2 = 0
  · have hcard : (mol.toMoleculeGraph.maximumMancudeMatchings attached).card = 2 := by
      rw [← hcount, hstats]
      simp [heven]
    have hpartnerSum :
        (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
            (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) =
          mol.atomZAt duplicated.val + mol.atomZAt alternate := by
      rw [← hsum, hstats]
      simp [heven]
    unfold simpleMancudeCycleLabel CIPAtomicLabel.toExactAtomicNumber
      CIPAtomicLabel.effectiveDenominator ExactAtomicNumber.value
      MoleculeGraph.exactMancudeAverage
    simp only [hlength, heven, beq_iff_eq, if_pos, hcard, hpartnerSum]
    rw [hduplicatedZ, halternateZ]
    norm_num
  · have hodd : (rest.length + 3) % 2 = 1 := by omega
    have hcard : (mol.toMoleculeGraph.maximumMancudeMatchings attached).card =
        rest.length + 3 := by
      rw [← hcount, hstats]
      simp [heven]
    have hpartnerSum :
        (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
            (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) =
          (rest.length + 3) / 2 *
            (mol.atomZAt duplicated.val + mol.atomZAt alternate) := by
      rw [← hsum, hstats]
      simp [heven]
    have hevenBool : ((rest.length + 3) % 2 == 0) = false := by simpa using heven
    unfold simpleMancudeCycleLabel CIPAtomicLabel.toExactAtomicNumber
      CIPAtomicLabel.effectiveDenominator ExactAtomicNumber.value
      MoleculeGraph.exactMancudeAverage
    simp only [hlength, hevenBool, Bool.false_eq_true, if_false, hcard, hpartnerSum]
    simp [hduplicatedZ, halternateZ]

/-- Structural discharge of the complete simple-cycle branch obligation. -/
theorem structuralMancudeRule1aSimpleCycleBranchSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) :
    mol.MancudeRule1aSimpleCycleBranchSound := by
  intro attached duplicated cycle alternate label hlocalized hcycle hlabel
  have hlabelEq : label = mol.simpleMancudeCycleLabel duplicated.val alternate cycle := by
    unfold mancudeRule1aLabel? at hlabel
    simp only [hlocalized, Bool.not_true, Bool.false_eq_true, if_false, hcycle,
      Option.some.injEq] at hlabel
    exact hlabel.symm
  subst label
  have haverage := mol.simpleMancudeCycleLabel_exactAverage hwellFormed hunique
    attached duplicated cycle alternate hcycle
  have hsemantic : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated :=
    (mol.containsUndirectedEdge_localizedMancudeEdges_iff
      hwellFormed hunique attached duplicated).1 hlocalized
  rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized hsemantic]
  exact haverage

end RawMolecule

end
end OneCenter
end TetraStereo
