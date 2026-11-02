import TetraStereo.OneCenter.CarbohydrateAppendixErrataGlossarySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

inductive ImageArtifactKind where
  | numberedOrChartStructure
  | genericGlossaryStructure
  | erratumCorrectedStructure
  | typographyGlyph
  deriving DecidableEq, Repr

structure ImageArtifactData where
  relativePath : String
  sha256 : String
  kind : ImageArtifactKind
  deriving DecidableEq, Repr

def ImageArtifactKind.requiresMolecularGraph : ImageArtifactKind → Bool
  | .numberedOrChartStructure | .genericGlossaryStructure | .erratumCorrectedStructure => true
  | .typographyGlyph => false

inductive TemplateNodeLabel where
  | carbon | ringOxygen | substituentOxygen | hydrogen | genericR | nucleotideDiphosphate
  | lysineNitrogen | glcNAcAnomericCarbon
  deriving DecidableEq, Repr

structure TemplateBond where
  low : Nat
  high : Nat
  deriving DecidableEq, Repr

structure StructureGraphTemplate where
  nodes : List TemplateNodeLabel
  bonds : List TemplateBond
  openValenceAt? : Option Nat := none
  reactionFocus? : Option TemplateBond := none
  unspecifiedAnomericBond : Bool := false
  deriving DecidableEq, Repr

def pyranoseRingNodes : List TemplateNodeLabel :=
  [ .ringOxygen, .carbon, .carbon, .carbon, .carbon, .carbon ]

def pyranoseRingBonds : List TemplateBond :=
  [ ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨0, 5⟩ ]

def glycoseTemplate : StructureGraphTemplate :=
  { nodes := pyranoseRingNodes ++ [.substituentOxygen, .hydrogen]
    bonds := pyranoseRingBonds ++ [⟨1, 6⟩, ⟨6, 7⟩]
    unspecifiedAnomericBond := true }

def glycosylTemplate : StructureGraphTemplate :=
  { nodes := pyranoseRingNodes
    bonds := pyranoseRingBonds
    openValenceAt? := some 1
    unspecifiedAnomericBond := true }

def glycosideTemplate : StructureGraphTemplate :=
  { nodes := pyranoseRingNodes ++ [.substituentOxygen, .genericR]
    bonds := pyranoseRingBonds ++ [⟨1, 6⟩, ⟨6, 7⟩]
    unspecifiedAnomericBond := true }

def glycosidaseTemplate : StructureGraphTemplate :=
  { nodes := pyranoseRingNodes ++ [.substituentOxygen, .genericR]
    bonds := pyranoseRingBonds ++ [⟨1, 6⟩, ⟨6, 7⟩]
    reactionFocus? := some ⟨1, 6⟩
    unspecifiedAnomericBond := true }

def glycosyltransferaseTemplate : StructureGraphTemplate :=
  { nodes := pyranoseRingNodes ++ [.substituentOxygen, .nucleotideDiphosphate]
    bonds := pyranoseRingBonds ++ [⟨1, 6⟩, ⟨6, 7⟩]
    reactionFocus? := some ⟨1, 6⟩
    unspecifiedAnomericBond := true }

/-- The erratum graphic says specifically that lysine nitrogen is bonded to GlcNAc C1. -/
def lysineGlcNAcC1Template : StructureGraphTemplate :=
  { nodes := [.lysineNitrogen, .glcNAcAnomericCarbon]
    bonds := [⟨0, 1⟩] }

def symbolicTemplate? : String → Option StructureGraphTemplate
  | "2carb/2C3gif/GLOSA.GIF" => some glycoseTemplate
  | "2carb/2C3gif/GLOSB.GIF" => some glycosylTemplate
  | "2carb/2C3gif/GLOSC.GIF" => some glycosideTemplate
  | "2carb/2C3gif/GLOSD.GIF" => some glycosidaseTemplate
  | "2carb/2C3gif/GLOSE.GIF" => some glycosyltransferaseTemplate
  | "2carb/2C3gif/LYGL1.GIF" => some lysineGlcNAcC1Template
  | _ => none

def StructureGraphTemplate.wellFormed (graph : StructureGraphTemplate) : Bool :=
  (graph.bonds.all fun bond =>
      bond.low < bond.high && bond.high < graph.nodes.length) &&
    (match graph.openValenceAt? with
      | none => true
      | some vertex => vertex < graph.nodes.length) &&
    (match graph.reactionFocus? with
      | none => true
      | some bond => bond ∈ graph.bonds)

def ImageArtifactData.symbolicTemplateTranscribed (data : ImageArtifactData) : Bool :=
  data.kind.requiresMolecularGraph && (symbolicTemplate? data.relativePath).isSome

inductive GraphAuditMaturity where
  | symbolicTemplateTranscribed
  | sourceOnlyGraphPending
  | nonChemicalGlyphAudited
  deriving DecidableEq, Repr

def ImageArtifactData.graphAuditMaturity (data : ImageArtifactData) : GraphAuditMaturity :=
  if data.symbolicTemplateTranscribed then .symbolicTemplateTranscribed
  else if data.kind.requiresMolecularGraph then .sourceOnlyGraphPending
  else .nonChemicalGlyphAudited

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
