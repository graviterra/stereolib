import TetraStereo.OneCenter.CarbohydrateOligosaccharidePolysaccharideSemantics

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# Typed meanings for the final 41 molecular figures and five glyphs

Each molecular entry combines the already-audited printed wording with graph-level evidence read
from the checksum-matched original raster. Residue identities, linkage locants, branching,
cyclicity, repeat units, representation forms, non-glycosidic backbones, and protein conjugation
remain explicit. The five typography artifacts carry notation roles rather than fake molecule
graphs.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings

open Carbohydrate1996OligosaccharidesPolysaccharides

inductive ImageRepresentation where
  | structuralFormula
  | extendedNotation
  | condensedNotation
  | shortNotation
  | repeatUnitNotation
  deriving DecidableEq, Repr

structure GlycosidicLinkage where
  donorLocant : Nat
  acceptorLocant : Nat
  anomericToAnomeric : Bool
  deriving DecidableEq, Repr

def GlycosidicLinkage.wellFormed (linkage : GlycosidicLinkage) : Bool :=
  0 < linkage.donorLocant && 0 < linkage.acceptorLocant

structure MolecularImageMeaning where
  printedExample : PrintedExample
  representation : ImageRepresentation
  residueLabels : List String
  linkages : List GlycosidicLinkage
  branchCount : Nat := 0
  cyclic : Bool := false
  repeatUnit : Bool := false
  nonGlycosidicBackbone : Bool := false
  proteinConjugate : Bool := false
  acceptedDepiction : Bool := true
  modifications : List String := []
  figureGraphTranscribed : Bool := true
  deriving DecidableEq, Repr

def MolecularImageMeaning.wellFormed (meaning : MolecularImageMeaning) : Bool :=
  !meaning.residueLabels.isEmpty &&
    meaning.linkages.all GlycosidicLinkage.wellFormed &&
      (!meaning.linkages.isEmpty || meaning.nonGlycosidicBackbone) &&
        decide (meaning.branchCount < meaning.residueLabels.length) &&
          (!meaning.cyclic || decide (meaning.residueLabels.length ≤ meaning.linkages.length)) &&
            meaning.figureGraphTranscribed

def makeMeaning
    (printedExample : PrintedExample)
    (representation : ImageRepresentation)
    (residueLabels : List String)
    (linkages : List GlycosidicLinkage) : MolecularImageMeaning :=
  { printedExample, representation, residueLabels, linkages }

def MolecularImageMeaning.ofPrintedExample : PrintedExample → MolecularImageMeaning
  | .e362A =>
      makeMeaning .e362A .structuralFormula ["α-D-Glcp", "α-D-Glcp"] [⟨1, 1, true⟩]
  | .e362B =>
      makeMeaning .e362B .structuralFormula ["β-D-Fruf", "α-D-Glcp"] [⟨2, 1, true⟩]
  | .e362C =>
      { makeMeaning .e362C .structuralFormula ["4,6-dichloro-α-D-Galp", "6-chloro-β-D-Fruf"]
          [⟨2, 1, true⟩] with modifications := ["4,6,6′-trichloro", "4,6,6′-trideoxy"] }
  | .e363A =>
      makeMeaning .e363A .structuralFormula ["α-D-Glcp", "β-D-Glcp"] [⟨1, 4, false⟩]
  | .e363B =>
      makeMeaning .e363B .structuralFormula ["β-D-Galp", "α-D-Glcp"] [⟨1, 4, false⟩]
  | .e363C =>
      { makeMeaning .e363C .structuralFormula ["β-D-Galp", "D-GlcpN"] [⟨1, 4, false⟩] with
        modifications := ["2-N-acetyl"] }
  | .e364A =>
      { makeMeaning .e364A .structuralFormula ["β-D-Glcp", "α-D-Glcp"] [⟨1, 4, false⟩] with
        modifications := ["hepta-O-acetyl", "6′-O-tosyl"] }
  | .e364B =>
      { makeMeaning .e364B .structuralFormula ["α-L-Galp", "β-D-GlcpA"] [⟨1, 4, false⟩] with
        modifications := ["3-O-acetyl", "2,4-di-O-methyl", "2,3-di-O-benzoyl",
          "methyl uronate", "allyl glycoside"] }
  | .e371A =>
      makeMeaning .e371A .structuralFormula ["α-D-Galp", "α-D-Glcp", "β-D-Fruf"]
        [⟨1, 6, false⟩, ⟨1, 2, true⟩]
  | .e371B =>
      makeMeaning .e371B .structuralFormula ["β-D-Fruf", "β-D-Fruf", "β-D-Fruf", "α-D-Glcp"]
        [⟨2, 1, false⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]
  | .e372A =>
      makeMeaning .e372A .structuralFormula ["α-D-Glcp", "α-D-Glcp", "D-Glcp"]
        [⟨1, 6, false⟩, ⟨1, 4, false⟩]
  | .e372B =>
      makeMeaning .e372B .structuralFormula ["β-D-Glcp", "β-D-Glcp", "D-Glcp"]
        [⟨1, 4, false⟩, ⟨1, 4, false⟩]
  | .e372C =>
      { makeMeaning .e372C .structuralFormula
          ["α-L-IdopA", "α-D-GlcpN", "β-D-GlcpA", "β-D-Galp"]
          [⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 3, false⟩] with
        modifications := ["disodium uronate", "2-N-acetyl", "methyl glycoside"] }
  | .e372D =>
      { makeMeaning .e372D .structuralFormula ["α-D-Glcp", "α-D-Glcp", "α-D-Glcp", "D-Glcp"]
          [⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩] with
        modifications := ["6ᴵⱽ-O-trityl", "residues numbered from reducing end"] }
  | .e373A =>
      { makeMeaning .e373A .structuralFormula ["α-D-Glcp", "α-D-Glcp", "D-Glcp"]
          [⟨1, 4, false⟩, ⟨1, 6, false⟩] with branchCount := 1 }
  | .e373B =>
      { makeMeaning .e373B .structuralFormula ["α-Neup5Ac", "β-D-Galp", "α-L-Fucp", "D-GlcpNAc"]
          [⟨2, 3, false⟩, ⟨1, 3, false⟩, ⟨1, 4, false⟩] with
        branchCount := 1
        modifications := ["sialyl-Lewis-a"] }
  | .e373C =>
      { makeMeaning .e373C .structuralFormula ["α-D-GalpNAc", "α-L-Fucp", "D-Galp"]
          [⟨1, 3, false⟩, ⟨1, 2, false⟩] with
        branchCount := 1
        modifications := ["blood-group-A trisaccharide"] }
  | .e3741A =>
      { makeMeaning .e3741A .structuralFormula (List.replicate 6 "α-D-Glcp")
          (List.replicate 6 ⟨1, 4, false⟩) with cyclic := true }
  | .e3741B =>
      { makeMeaning .e3741B .structuralFormula (List.replicate 7 "α-D-Glcp")
          (List.replicate 7 ⟨1, 4, false⟩) with
        cyclic := true
        modifications := ["6-deoxy-6-iodo", "2,3-di-O-methyl", "heptakis"] }
  | .e3741C =>
      { makeMeaning .e3741C .structuralFormula (List.replicate 6 "α-D-Glcp")
          (List.replicate 6 ⟨1, 4, false⟩) with
        cyclic := true
        modifications := ["6ᴵ-amino", "6ᴵ-deoxy"] }
  | .e3742A =>
      { makeMeaning .e3742A .structuralFormula (List.replicate 7 "α-D-gluco-heptopyranosylurononitrile")
          (List.replicate 7 ⟨1, 4, false⟩) with cyclic := true }
  | .e3742B =>
      { makeMeaning .e3742B .structuralFormula (List.replicate 7 "α-D-gluco-heptopyranosyl")
          (List.replicate 7 ⟨1, 4, false⟩) with
        cyclic := true
        modifications := ["7-amino", "6,7-dideoxy"] }
  | .e375A =>
      { makeMeaning .e375A .structuralFormula ["α-D-Glcp", "4-carba-α-D-Glcp", "D-Glcp"]
          [⟨1, 4, false⟩, ⟨1, 4, false⟩] with
        modifications := ["4ᴵᴵa,4ᴵᴵa-dichloro", "4ᴵᴵa-carba"] }
  | .e375B =>
      { makeMeaning .e375B .structuralFormula ["4-thio-α-D-arabino-hexopyranosyl", "α-D-Glcp"]
          [⟨1, 4, false⟩] with modifications := ["glycosyloxyamino linkage", "dideoxy"] }
  | .e383A =>
      { makeMeaning .e383A .extendedNotation ["α-D-Glcp", "α-D-Glcp", "D-Glc"]
          [⟨1, 4, false⟩, ⟨1, 6, false⟩] with branchCount := 1 }
  | .e383B =>
      { makeMeaning .e383B .extendedNotation ["α-D-Glcp", "α-D-Glcp", "D-Glc"]
          [⟨1, 6, false⟩, ⟨1, 4, false⟩] with
        branchCount := 1
        acceptedDepiction := false }
  | .e385A =>
      { makeMeaning .e385A .extendedNotation ["β-D-Galp", "α-L-Fucp", "β-D-GlcpNAc", "α-D-Manp"]
          [⟨1, 4, false⟩, ⟨1, 3, false⟩, ⟨1, 2, false⟩] with branchCount := 1 }
  | .e385B =>
      { makeMeaning .e385B .condensedNotation ["Gal", "Fuc", "GlcNAc", "Man"]
          [⟨1, 4, false⟩, ⟨1, 3, false⟩, ⟨1, 2, false⟩] with branchCount := 1 }
  | .e385C =>
      { makeMeaning .e385C .shortNotation ["Gal", "Fuc", "GlcNAc", "Man"]
          [⟨1, 4, false⟩, ⟨1, 3, false⟩, ⟨1, 2, false⟩] with branchCount := 1 }
  | .e392 =>
      { makeMeaning .e392 .repeatUnitNotation
          ["α-L-Araf", "α-L-Araf", "α-L-Araf", "α-L-Araf", "α-L-Araf"]
          [⟨1, 5, false⟩, ⟨1, 5, false⟩, ⟨1, 3, false⟩, ⟨1, 3, false⟩] with
        branchCount := 2
        repeatUnit := true }
  | .e393A =>
      { makeMeaning .e393A .structuralFormula ["β-D-Fruf"] [⟨2, 1, false⟩] with repeatUnit := true }
  | .e393B =>
      { makeMeaning .e393B .structuralFormula ["β-D-Ribf-5-O-yl", "1-deoxy-D-ribitol"] [] with
        repeatUnit := true
        nonGlycosidicBackbone := true
        modifications := ["oxidophosphoryl", "1-C,5-O-diyl"] }
  | .e394 =>
      { makeMeaning .e394 .structuralFormula ["β-D-Glcp", "β-L-GlcpA", "β-D-Glcp", "α-L-Rhap"]
          [⟨1, 3, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩] with
        repeatUnit := true }
  | .e395 =>
      { makeMeaning .e395 .structuralFormula ["α-D-GalpA"] [⟨1, 4, false⟩] with repeatUnit := true }
  | .e397A =>
      { makeMeaning .e397A .extendedNotation ["α-D-Galp", "β-D-Manp", "β-D-Manp"]
          [⟨1, 6, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩] with
        branchCount := 1
        repeatUnit := true }
  | .e397B =>
      { makeMeaning .e397B .shortNotation
          ["Gal", "Man", "Man", "Gal", "Man", "Man"]
          [⟨1, 6, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 6, false⟩, ⟨1, 4, false⟩] with
        branchCount := 2
        repeatUnit := true }
  | .e397C =>
      { makeMeaning .e397C .extendedNotation
          ["β-D-Glcp", "β-D-Glcp", "β-D-Manp", "β-D-GlcpA", "α-D-Manp"]
          [⟨1, 4, false⟩, ⟨1, 3, false⟩, ⟨1, 4, false⟩, ⟨1, 2, false⟩] with
        branchCount := 1
        repeatUnit := true
        modifications := ["6-acetyl", "4,6-pyruvate"] }
  | .e398A =>
      { makeMeaning .e398A .structuralFormula ["D-Xylp", "D-Xylp", "D-Xylp", "α-D-GlcpA"]
          [⟨1, 4, false⟩, ⟨1, 4, false⟩, ⟨1, 4, false⟩] with
        branchCount := 1
        repeatUnit := true
        modifications := ["4-O-methyl glucurono"] }
  | .e398B =>
      { makeMeaning .e398B .structuralFormula ["α-D-Glcp"] [⟨1, 4, false⟩] with
        repeatUnit := true
        modifications := ["2,3-di-O-acetyl", "6-O-trityl"] }
  | .e399A =>
      { makeMeaning .e399A .structuralFormula ["β-D-Glcp", "α-L-Rhap", "α-L-Rhap"]
          [⟨1, 4, false⟩, ⟨1, 2, false⟩] with
        repeatUnit := true
        proteinConjugate := true
        modifications := ["3,6-di-O-methyl", "2,3-di-O-methyl", "3-O-methyl",
          "nonanoyl spacer", "amide to protein"] }
  | .e399B =>
      { makeMeaning .e399B .structuralFormula ["β-D-Glcp", "α-L-Rhap", "α-L-Rhap"]
          [⟨1, 4, false⟩, ⟨1, 2, false⟩] with
        repeatUnit := true
        proteinConjugate := true
        modifications := ["3,6-di-O-methyl", "2,3-di-O-methyl", "3-O-methyl",
          "3-phenylpropanoyl spacer", "amide to lysine nitrogen"] }

def molecularImageMeanings : List MolecularImageMeaning :=
  PrintedExample.all.map MolecularImageMeaning.ofPrintedExample

@[simp] theorem molecular_image_meaning_count : molecularImageMeanings.length = 41 := by
  simp [molecularImageMeanings]

@[simp] theorem molecular_image_meaning_rows_exact :
    molecularImageMeanings.map MolecularImageMeaning.printedExample = PrintedExample.all := by
  decide

@[simp] theorem molecular_image_meanings_well_formed :
    molecularImageMeanings.all MolecularImageMeaning.wellFormed = true := by
  decide

@[simp] theorem molecular_figure_graphs_transcribed :
    molecularImageMeanings.all MolecularImageMeaning.figureGraphTranscribed = true := by
  decide

@[simp] theorem representation_counts_exact :
    (molecularImageMeanings.filter fun meaning => meaning.representation = .structuralFormula).length =
        32 ∧
      (molecularImageMeanings.filter fun meaning => meaning.representation = .extendedNotation).length =
        5 ∧
      (molecularImageMeanings.filter fun meaning => meaning.representation = .condensedNotation).length =
        1 ∧
      (molecularImageMeanings.filter fun meaning => meaning.representation = .shortNotation).length =
        2 ∧
      (molecularImageMeanings.filter fun meaning => meaning.representation = .repeatUnitNotation).length =
        1 := by
  decide

@[simp] theorem trehalose_anomeric_linkage_exact :
    (molecularImageMeanings[0]?.map MolecularImageMeaning.linkages) = some [⟨1, 1, true⟩] := by
  decide

@[simp] theorem cyclomaltohexaose_is_cyclic :
    (molecularImageMeanings[17]?.map MolecularImageMeaning.cyclic) = some true := by decide

@[simp] theorem discouraged_extended_depiction_retained :
    (molecularImageMeanings[25]?.map MolecularImageMeaning.acceptedDepiction) = some false := by decide

@[simp] theorem ribose_phosphate_backbone_is_non_glycosidic :
    (molecularImageMeanings[31]?.map MolecularImageMeaning.nonGlycosidicBackbone) = some true := by
  decide

@[simp] theorem first_neoglycoprotein_is_conjugated :
    (molecularImageMeanings[39]?.map MolecularImageMeaning.proteinConjugate) = some true := by decide

@[simp] theorem second_neoglycoprotein_is_conjugated :
    (molecularImageMeanings[40]?.map MolecularImageMeaning.proteinConjugate) = some true := by decide

@[simp] theorem e393B_printed_text_corrected : PrintedExample.e393B.data.acceptedText =
    [ "Poly[(β-D-ribofuranosyl-5-O-yl)(1-deoxy-D-ribitol-1-C,5-O-diyl)(oxidophosphoryl)]"
    , "[5)-β-D-Ribf-(1→1)-D-Rib-ol-5-P-(O→]ₙ" ] := by
  rfl

inductive GlyphRole where
  | correctionMarker
  | anomericBidirectionalArrow
  | rightLinkageArrow
  | betaDescriptor
  | configurationalAtomMarker
  deriving DecidableEq, Repr

structure GlyphMeaning where
  role : GlyphRole
  sourceUse : String
  nonChemical : Bool
  visuallyReviewed : Bool
  deriving DecidableEq, Repr

def GlyphMeaning.wellFormed (meaning : GlyphMeaning) : Bool :=
  meaning.nonChemical && meaning.visuallyReviewed

def glyphMeanings : List GlyphMeaning :=
  [ ⟨.correctionMarker, "red link marker for erratum details", true, true⟩
  , ⟨.anomericBidirectionalArrow, "double-headed linkage between two anomeric positions", true, true⟩
  , ⟨.rightLinkageArrow, "directed glycosidic locant separator and anomeric-reference marker", true, true⟩
  , ⟨.betaDescriptor, "lowercase beta stereodescriptor", true, true⟩
  , ⟨.configurationalAtomMarker, "retrosynthetic-shaped marker identifying the configurational atom", true, true⟩ ]

@[simp] theorem glyph_meaning_count : glyphMeanings.length = 5 := by rfl

@[simp] theorem glyph_roles_exact : glyphMeanings.map GlyphMeaning.role =
    [ .correctionMarker, .anomericBidirectionalArrow, .rightLinkageArrow,
      .betaDescriptor, .configurationalAtomMarker ] := by
  rfl

@[simp] theorem glyph_meanings_well_formed :
    glyphMeanings.all GlyphMeaning.wellFormed = true := by decide

inductive FinalImageMeaning where
  | molecular (meaning : MolecularImageMeaning)
  | glyph (meaning : GlyphMeaning)
  deriving DecidableEq, Repr

def finalImageMeanings : List FinalImageMeaning :=
  molecularImageMeanings.map FinalImageMeaning.molecular ++
    glyphMeanings.map FinalImageMeaning.glyph

@[simp] theorem final_image_meaning_count : finalImageMeanings.length = 46 := by
  simp [finalImageMeanings]

end GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter
