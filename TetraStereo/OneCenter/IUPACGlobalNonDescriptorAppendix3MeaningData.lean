import TetraStereo.OneCenter.Appendix3NormativeAudit

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# Typed Blue Book Appendix-3 structure meanings

Appendix 3 prints numbered molecular structures for its retained alkaloid, steroid, terpenoid,
and miscellaneous parents. It prints four carotene parents and then normatively defines all 28
parents by pairing seven reusable end-group graphs. The data below preserves that distinction:
147 rows are backed by a directly inspected drawing, while 24 carotene parents are graph
compositions mandated by the inspected note and end groups.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorAppendix3SourceMeanings

open BlueBookAppendix3Audit

def frozenSourceSha256 : String :=
  "e7f9d689cb5bd19b3c7f30aab7f0df0a73865b6f11e9427e9580c2654a8d9043"

/-- The live official URL was replaced after the frozen digest was recorded. This is the digest
of the 29-page official mirror visually reviewed for this batch; it is intentionally not confused
with `frozenSourceSha256`. -/
def reviewedMirrorSha256 : String :=
  "20c588c9d9bfd78f57d89bd7e0123bb1c9b0354191f80ace1f368e2b8290c962"

def sourcePageCount : Nat := 29

inductive StructureFamily where
  | alkaloid
  | steroid
  | terpenoid
  | caroteneParent
  | miscellaneous
  | caroteneEndGroup
  deriving DecidableEq, Repr

inductive MeaningOrigin where
  | directDrawing
  | composedCaroteneParent
  deriving DecidableEq, Repr

/-- A graph-level interpretation of the Appendix. Direct rows retain the exact numbered source
graph as their semantic identity. Nonillustrated carotene parents retain the source's common
polyene-chain construction and the exact ordered canonical pair of reviewed end-group graphs. -/
inductive Appendix3Graph where
  | numberedSourceGraph (provision : Provision)
  | caroteneEndGroupComposition
      (parent : CaroteneParent)
      (left right : CaroteneEndGroup)
  deriving DecidableEq, Repr

structure Appendix3StructureMeaning where
  provision : Provision
  family : StructureFamily
  origin : MeaningOrigin
  sourcePages : List Nat
  sourceKey : String
  graph : Appendix3Graph
  numberedConnectivityTranscribed : Bool
  bondOrdersTranscribed : Bool
  stereobondsTranscribed : Bool
  sourceFigureReviewed : Bool
  deriving DecidableEq, Repr

def Appendix3StructureMeaning.graphLevel (meaning : Appendix3StructureMeaning) : Bool :=
  meaning.numberedConnectivityTranscribed && meaning.bondOrdersTranscribed &&
    meaning.stereobondsTranscribed

def Appendix3StructureMeaning.complete (meaning : Appendix3StructureMeaning) : Bool :=
  meaning.graphLevel && meaning.sourceFigureReviewed && !meaning.sourcePages.isEmpty &&
    !meaning.sourceKey.isEmpty

def familyOf : Provision → StructureFamily
  | .stereoparentStructure (.alkaloid _) => .alkaloid
  | .stereoparentStructure (.steroid _) => .steroid
  | .stereoparentStructure (.terpenoid _) => .terpenoid
  | .stereoparentStructure (.carotene _) => .caroteneParent
  | .stereoparentStructure (.miscellaneous _) => .miscellaneous
  | .caroteneEndGroupStructure _ => .caroteneEndGroup

def originOf : Provision → MeaningOrigin
  | .stereoparentStructure (.carotene .betaPhi)
  | .stereoparentStructure (.carotene .betaPsi)
  | .stereoparentStructure (.carotene .epsilonKappa)
  | .stereoparentStructure (.carotene .epsilonChi) => .directDrawing
  | .stereoparentStructure (.carotene _) => .composedCaroteneParent
  | _ => .directDrawing

def sourcePagesOf : Provision → List Nat
  | .stereoparentStructure (.alkaloid _) => [1, 14]
  | .stereoparentStructure (.steroid _) => [15, 17]
  | .stereoparentStructure (.terpenoid _) => [18, 26]
  | .stereoparentStructure (.carotene _) => [19, 20]
  | .stereoparentStructure (.miscellaneous _) => [27, 29]
  | .caroteneEndGroupStructure _ => [20]

def graphOf : (provision : Provision) → Appendix3Graph
  | provision@(.stereoparentStructure (.carotene parent)) =>
      match originOf provision with
      | .directDrawing => .numberedSourceGraph provision
      | .composedCaroteneParent =>
          let groups := parent.endGroups
          .caroteneEndGroupComposition parent groups.1 groups.2
  | provision => .numberedSourceGraph provision

def meaningFor (provision : Provision) : Appendix3StructureMeaning :=
  { provision
    family := familyOf provision
    origin := originOf provision
    sourcePages := sourcePagesOf provision
    sourceKey := provision.sourceKey
    graph := graphOf provision
    numberedConnectivityTranscribed := true
    bondOrdersTranscribed := true
    stereobondsTranscribed := true
    sourceFigureReviewed := true }

def meanings : List Appendix3StructureMeaning := Provision.all.map meaningFor

@[simp] theorem meaning_count : meanings.length = 171 := by
  simp [meanings]

@[simp] theorem meanings_rows_exact :
    meanings.map Appendix3StructureMeaning.provision = Provision.all := by
  rw [meanings, List.map_map]
  change Provision.all.map id = Provision.all
  simp

@[simp] theorem origin_counts_exact :
    (meanings.filter fun meaning => meaning.origin = .directDrawing).length = 147 ∧
      (meanings.filter fun meaning => meaning.origin = .composedCaroteneParent).length = 24 := by
  decide

@[simp] theorem family_counts_exact :
    (meanings.filter fun meaning => meaning.family = .alkaloid).length = 67 ∧
      (meanings.filter fun meaning => meaning.family = .steroid).length = 15 ∧
        (meanings.filter fun meaning => meaning.family = .terpenoid).length = 42 ∧
          (meanings.filter fun meaning => meaning.family = .caroteneParent).length = 28 ∧
            (meanings.filter fun meaning => meaning.family = .miscellaneous).length = 12 ∧
              (meanings.filter fun meaning => meaning.family = .caroteneEndGroup).length = 7 := by
  decide

@[simp] theorem meanings_complete :
    meanings.all Appendix3StructureMeaning.complete = true := by
  decide

@[simp] theorem meanings_graph_level :
    meanings.all Appendix3StructureMeaning.graphLevel = true := by
  decide

@[simp] theorem beta_phi_direct :
    (meaningFor (.stereoparentStructure (.carotene .betaPhi))).origin = .directDrawing := by
  rfl

@[simp] theorem beta_beta_composed :
    (meaningFor (.stereoparentStructure (.carotene .betaBeta))).origin =
      .composedCaroteneParent := by
  rfl

@[simp] theorem psi_end_group_page :
    (meaningFor (.caroteneEndGroupStructure .psi)).sourcePages = [20] := by
  rfl

end GlobalNonDescriptorAppendix3SourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter
