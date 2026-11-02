import TetraStereo.OneCenter.AuthoritativeSemanticMancudeDescriptorInvariance
import TetraStereo.OneCenter.CIPAuthoritativeRule6P92Enumeration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Rule-6 transport over the canonical mancude comparator

The Rule-6 reference-family algorithms are representation-independent once supplied a ranking
backend.  This module proves that every backend constructed as a function of the canonical
Rules-1a--5 comparison oracle, including the two- and three-group common-reference routes and the
dependent four-way route, is exactly Kekule-choice invariant.

The theorem is deliberately polymorphic in the backend builder.  It therefore covers the existing
occurrence backend and any later source-level implementation without duplicating the Rule-6 proof.
-/

open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration

namespace SemanticMolecule

/-- Build a Rule-6 position-ranking backend only from the complete canonical comparison oracle. -/
def aromaticCanonicalRule6Backend (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend) :
    ProductionRule6RankingBackend :=
  build (source.compareAromaticCanonical? selection fuel center ligand context)

/-- Every comparison-derived Rule-6 backend is exactly independent of Kekule choice. -/
theorem aromaticCanonicalRule6Backend_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend) :
    source.aromaticCanonicalRule6Backend leftSelection fuel center ligand context build =
      source.aromaticCanonicalRule6Backend rightSelection fuel center ligand context build := by
  unfold aromaticCanonicalRule6Backend
  rw [source.compareAromaticCanonical_function_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand context]

/-- Exact two-group/common-reference Rule-6 descriptor projection. -/
def aromaticCanonicalRule6FamilyDescriptor? (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) : Option RS :=
  rule6FamilyDescriptorWithBackend?
    (source.aromaticCanonicalRule6Backend selection fuel center ligand context build)
    parity references

/-- Family emission has exactly the independently stated common strict-reference meaning. -/
theorem aromaticCanonicalRule6FamilyDescriptor?_eq_some_iff_commonDescriptor
    (source : SemanticMolecule) (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule6FamilyDescriptor? selection fuel center ligand context
        build parity references = some descriptor ↔
      CommonRule6Descriptor
        (source.aromaticCanonicalRule6Backend selection fuel center ligand context build)
        parity references descriptor := by
  exact rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor _ _ _ _

/-- Two-group/common-reference Rule 6 is exactly Kekule-choice invariant. -/
theorem aromaticCanonicalRule6FamilyDescriptor?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) :
    source.aromaticCanonicalRule6FamilyDescriptor? leftSelection fuel center ligand context
        build parity references =
      source.aromaticCanonicalRule6FamilyDescriptor? rightSelection fuel center ligand context
        build parity references := by
  unfold aromaticCanonicalRule6FamilyDescriptor?
  rw [source.aromaticCanonicalRule6Backend_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand context build]

/-- Exact three-group singleton-reference route, including its prescribed descriptor reversal. -/
def aromaticCanonicalRule6ThreeGroupDescriptor? (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS := do
  let descriptor ← source.aromaticCanonicalRule6FamilyDescriptor? selection fuel center ligand
    context build parity (rule6ThreeGroupReferencePositions sorted)
  some (RS.swap descriptor)

/-- The complete three-group Rule-6 route is exactly Kekule-choice invariant. -/
theorem aromaticCanonicalRule6ThreeGroupDescriptor?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) :
    source.aromaticCanonicalRule6ThreeGroupDescriptor? leftSelection fuel center ligand context
        build parity sorted =
      source.aromaticCanonicalRule6ThreeGroupDescriptor? rightSelection fuel center ligand context
        build parity sorted := by
  unfold aromaticCanonicalRule6ThreeGroupDescriptor?
  rw [source.aromaticCanonicalRule6FamilyDescriptor?_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand context build parity
    (rule6ThreeGroupReferencePositions sorted)]

/-- Exact dependent four-way Rule-6 carrier route. -/
def aromaticCanonicalRule6FourWayDescriptor? (source : SemanticMolecule)
    (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS :=
  authoritativeOccurrenceRule6FourWayDescriptor?
    (source.aromaticCanonicalRule6Backend selection fuel center ligand context build)
    parity sorted

/-- Four-way emission has exactly the independently stated dependent two-reference carrier
judgment. -/
theorem aromaticCanonicalRule6FourWayDescriptor?_eq_some_iff_judgment
    (source : SemanticMolecule) (selection : List (Nat × Nat)) (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection selection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection selection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule6FourWayDescriptor? selection fuel center ligand context
        build parity sorted = some descriptor ↔
      AuthoritativeFourWayDescriptorJudgment
        (source.aromaticCanonicalRule6Backend selection fuel center ligand context build)
        parity sorted descriptor := by
  exact authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment _ _ _ _

/-- The dependent four-way Rule-6 route is exactly Kekule-choice invariant. -/
theorem aromaticCanonicalRule6FourWayDescriptor?_kekule_invariant
    (source : SemanticMolecule)
    (leftSelection rightSelection : List (Nat × Nat))
    (leftExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection leftSelection))
    (rightExact : source.SemanticAromaticMancudeEdgeSetExact
      (source.withAromaticKekuleSelection rightSelection))
    (fuel : Nat)
    (center : Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (ligand : Fin 4 → Fin (source.withAromaticKekuleSelection leftSelection).atomCount)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (build : CanonicalMancudeTetrahedral.Comparison → ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) :
    source.aromaticCanonicalRule6FourWayDescriptor? leftSelection fuel center ligand context
        build parity sorted =
      source.aromaticCanonicalRule6FourWayDescriptor? rightSelection fuel center ligand context
        build parity sorted := by
  unfold aromaticCanonicalRule6FourWayDescriptor?
  rw [source.aromaticCanonicalRule6Backend_kekule_invariant
    leftSelection rightSelection leftExact rightExact fuel center ligand context build]

end SemanticMolecule

end TetraStereo.OneCenter
