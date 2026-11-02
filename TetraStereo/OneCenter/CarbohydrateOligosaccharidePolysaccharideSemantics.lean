import TetraStereo.OneCenter.CarbohydrateGlycosideRingSystemSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent oligosaccharide and polysaccharide semantics

This module audits the final numbered sections, 2-Carb-36 through 2-Carb-39, of the 1996
carbohydrate recommendations.  Numbered examples, the complete retained-disaccharide table, and
every row of the monosaccharide-symbol table are first-class obligations rather than comments.

This is still a source-level semantic transcription.  It deliberately does not claim that a
production molecule graph has yet been refined into these structures or that a formatter has yet
been proved to emit all of these names and symbols.
-/

namespace Carbohydrate1996OligosaccharidesPolysaccharides

inductive PrintedExample where
  | e362A | e362B | e362C
  | e363A | e363B | e363C
  | e364A | e364B
  | e371A | e371B
  | e372A | e372B | e372C | e372D
  | e373A | e373B | e373C
  | e3741A | e3741B | e3741C
  | e3742A | e3742B
  | e375A | e375B
  | e383A | e383B
  | e385A | e385B | e385C
  | e392
  | e393A | e393B
  | e394 | e395
  | e397A | e397B | e397C
  | e398A | e398B
  | e399A | e399B
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .e362A, .e362B, .e362C, .e363A, .e363B, .e363C, .e364A, .e364B
  , .e371A, .e371B, .e372A, .e372B, .e372C, .e372D, .e373A, .e373B, .e373C
  , .e3741A, .e3741B, .e3741C, .e3742A, .e3742B, .e375A, .e375B
  , .e383A, .e383B, .e385A, .e385B, .e385C
  , .e392, .e393A, .e393B, .e394, .e395, .e397A, .e397B, .e397C
  , .e398A, .e398B, .e399A, .e399B
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem length_all : all.length = 41 := by decide

end PrintedExample

def PrintedExample.sourceKey : PrintedExample → String
  | .e362A => "2-Carb-36.2/362A" | .e362B => "2-Carb-36.2/362B"
  | .e362C => "2-Carb-36.2/362C"
  | .e363A => "2-Carb-36.3/363A" | .e363B => "2-Carb-36.3/363B"
  | .e363C => "2-Carb-36.3/363C"
  | .e364A => "2-Carb-36.4/364A" | .e364B => "2-Carb-36.4/364B"
  | .e371A => "2-Carb-37.1/371A" | .e371B => "2-Carb-37.1/371B"
  | .e372A => "2-Carb-37.2/372A" | .e372B => "2-Carb-37.2/372B"
  | .e372C => "2-Carb-37.2/372C" | .e372D => "2-Carb-37.2/372D"
  | .e373A => "2-Carb-37.3/373A" | .e373B => "2-Carb-37.3/373B"
  | .e373C => "2-Carb-37.3/373C"
  | .e3741A => "2-Carb-37.4.1/3741A" | .e3741B => "2-Carb-37.4.1/3741B"
  | .e3741C => "2-Carb-37.4.1/3741C"
  | .e3742A => "2-Carb-37.4.2/3742A" | .e3742B => "2-Carb-37.4.2/3742B"
  | .e375A => "2-Carb-37.5/375A" | .e375B => "2-Carb-37.5/375B"
  | .e383A => "2-Carb-38.3/383A" | .e383B => "2-Carb-38.3/383B"
  | .e385A => "2-Carb-38.5/385A" | .e385B => "2-Carb-38.5/385B"
  | .e385C => "2-Carb-38.5/385C"
  | .e392 => "2-Carb-39.2/392"
  | .e393A => "2-Carb-39.3/393A" | .e393B => "2-Carb-39.3/393B"
  | .e394 => "2-Carb-39.4/394" | .e395 => "2-Carb-39.5/395"
  | .e397A => "2-Carb-39.7/397A" | .e397B => "2-Carb-39.7/397B"
  | .e397C => "2-Carb-39.7/397C"
  | .e398A => "2-Carb-39.8/398A" | .e398B => "2-Carb-39.8/398B"
  | .e399A => "2-Carb-39.9/399A" | .e399B => "2-Carb-39.9/399B"

structure PrintedExampleData where
  sourceURL : String
  sourceKey : String
  acceptedText : List String
  discouragedText : List String
  trivialNames : List String
  figureGraphTranscribed : Bool
  deriving DecidableEq, Repr

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .e362A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.2/362A",
        ["α-D-Glucopyranosyl α-D-glucopyranoside", "α-D-Glcp-(1↔1)-α-D-Glcp"], [],
        ["α,α-trehalose"], false⟩
  | .e362B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.2/362B",
        ["β-D-Fructofuranosyl α-D-glucopyranoside", "β-D-Fruf-(2↔1)-α-D-Glcp"],
        ["α-D-Glucopyranosyl β-D-fructofuranoside"], ["sucrose", "saccharose"], false⟩
  | .e362C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.2/362C",
        ["4,6,6′-Trichloro-4,6,6′-trideoxygalactosucrose",
          "6-Chloro-6-deoxy-β-D-fructofuranosyl " ++
            "4,6-dichloro-4,6-dideoxy-α-D-galactopyranoside"], [],
        ["galactosucrose (the 4-epimer of sucrose)"], false⟩
  | .e363A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.3/363A",
        ["α-D-Glucopyranosyl-(1→4)-β-D-glucopyranose", "α-D-Glcp-(1→4)-β-D-Glcp",
          "4-O-α-D-glucopyranosyl-β-D-glucopyranose"],
        ["β-D-maltose"], ["β-maltose"], false⟩
  | .e363B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.3/363B",
        ["β-D-Galactopyranosyl-(1→4)-α-D-glucopyranose", "β-D-Galp-(1→4)-α-D-Glcp",
          "4-O-β-D-galactopyranosyl-α-D-glucopyranose"],
        ["α-D-lactose"], ["α-lactose"], false⟩
  | .e363C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.3/363C",
        ["β-D-Galactopyranosyl-(1→4)-N-acetyl-D-glucosamine"], [],
        ["N-acetyllactosamine", "LacNAc"], false⟩
  | .e364A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.4/364A",
        ["1,2,2′,3,3′,4′,6-Hepta-O-acetyl-6′-O-tosyl-α-cellobiose",
          "2,3,4-Tri-O-acetyl-6-O-tosyl-β-D-glucopyranosyl-(1→4)-" ++
            "1,2,3,6-tetra-O-acetyl-α-D-glucopyranose"], [], [], false⟩
  | .e364B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/36.html", "2-Carb-36.4/364B",
        ["Methyl (3-O-acetyl-6-deoxy-2,4-di-O-methyl-α-L-galactpyranosyl)-(1→4)-" ++
          "(allyl 2,3-di-O-benzoyl-β-D-glucopyranosid)uronate"], [], [], false⟩
  | .e371A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.1/371A",
        ["β-D-Fructofuranosyl α-D-galactopyranosyl-(1→6)-α-D-glucopyranoside",
          "α-D-Galactopyranosyl-(1→6)-α-D-glucopyranosyl β-D-fructofuranoside",
          "α-D-Galp-(1→6)-α-D-Glcp-(1↔2)-β-D-Fruf"], [], ["raffinose"], false⟩
  | .e371B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.1/371B",
        ["β-D-Fructofuranosyl-(2→1)-β-D-fructofuranosyl-(2→1)-" ++
          "β-D-fructofuranosyl α-D-glucopyranoside",
          "β-D-Fruf-(2→1)-β-D-Fruf-(2→1)-β-D-Fruf-(2↔1)-α-D-Glcp"], [],
        ["nystose"], false⟩
  | .e372A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.2/372A",
        ["α-D-Glucopyranosyl-(1→6)-α-D-glucopyranosyl-(1→4)-D-glucopyranose"], [],
        ["panose"], false⟩
  | .e372B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.2/372B",
        ["β-D-Glucopyranosyl-(1→4)-β-D-glucopyranosyl-(1→4)-D-glucopyranose"], [],
        ["cellotriose"], false⟩
  | .e372C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.2/372C",
        ["Methyl (sodium α-L-idopyranosyluronate)-(1→4)-" ++
          "(2-acetamido-2-deoxy-α-D-glucopyranosyl)-(1→4)-" ++
          "(sodium β-D-glucopyranosyluronate)-(1→3)-β-D-galactopyranoside",
          "Na₂[α-L-IdopA-(1→4)-α-D-GlcpNAc-(1→4)-β-D-GlcpA-(1→3)-β-D-GalpOMe]"],
        [], [], false⟩
  | .e372D =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.2/372D",
        ["6ᴵⱽ-O-Tritylmaltotetraose"], [], [], false⟩
  | .e373A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.3/373A",
        ["α-D-Glucopyranosyl-(1→4)-[α-D-glucopyranosyl-(1→6)]-D-glucopyranose",
          "4,6-Di-O-(α-D-glucopyranosyl)-D-glucopyranose"], [], ["isopanose"], false⟩
  | .e373B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.3/373B",
        ["(5-Acetamido-3,5-dideoxy-D-glycero-α-D-galacto-non-2-ulopyranosylonic acid)-" ++
          "(2→3)-β-D-galactopyranosyl-(1→3)-[α-L-fucopyranosyl-(1→4)]-" ++
          "2-acetamido-2-deoxy-D-glucopyranose",
          "5-N-Acetyl-α-neuraminyl-(2→3)-β-D-galactopyranosyl-(1→3)-" ++
          "[α-L-fucopyranosyl-(1→4)]-2-acetamido-2-deoxy-D-glucopyranose",
          "α-Neup5Ac-(2→3)-β-D-Galp-(1→3)-[α-L-Fucp-(1→4)]-D-GlcpNAc"], [],
        ["sialyl-Leᵃ trisaccharide"], false⟩
  | .e373C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.3/373C",
        ["2-Acetamido-2-deoxy-α-D-galactopyranosyl-(1→3)-" ++
          "[α-L-fucopyranosyl-(1→2)]-D-galactopyranose",
          "α-D-GalpNAc-(1→3)-[α-L-Fucp-(1→2)]-D-Galp"], [],
        ["blood group A trisaccharide"], false⟩
  | .e3741A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.4.1/3741A",
        ["Cyclomaltohexaose"], [], ["α-cyclodextrin", "α-CD"], false⟩
  | .e3741B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.4.1/3741B",
        ["Heptakis(6-deoxy-6-iodo-2,3-di-O-methyl)cyclomaltoheptaose"], [], [], false⟩
  | .e3741C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.4.1/3741C",
        ["6ᴵ-Amino-6ᴵ-deoxycyclomaltohexaose"], [], [], false⟩
  | .e3742A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.4.2/3742A",
        ["Cycloheptakis-(1→4)-(6-deoxy-α-D-gluco-heptopyranosylurononitrile)"], [], [], false⟩
  | .e3742B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.4.2/3742B",
        ["Cycloheptakis-(1→4)-(7-amino-6,7-dideoxy-α-D-gluco-heptopyranosyl)"], [], [], false⟩
  | .e375A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.5/375A",
        ["4ᴵᴵa,4ᴵᴵa-Dichloro-4ᴵᴵa-carba-α-maltotriose"], [], [], false⟩
  | .e375B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/37.html", "2-Carb-37.5/375B",
        ["4-(2,6-Dideoxy-4-thio-α-D-arabino-hexopyranosyloxyamino)-" ++
          "4,6-dideoxy-α-D-glucopyranose"], [], [], false⟩
  | .e383A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/38.html", "2-Carb-38.3/383A",
        ["α-D-Glcp-(1→4)[α-D-Glcp-(1→6)]-D-Glc",
          "for 4,6-Di-O-α-D-glucopyranosyl-D-glucose"], [], [], false⟩
  | .e383B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/38.html", "2-Carb-38.3/383B", [],
        ["not [the alternate branched extended-form depiction]",
          "for 4,6-Di-O-α-D-glucopyranosyl-D-glucose"], [], false⟩
  | .e385A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/38.html", "2-Carb-38.5/385A",
        ["(a) extended form"], [], [], false⟩
  | .e385B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/38.html", "2-Carb-38.5/385B",
        ["(b) condensed form in two lines",
          "or in one line: Gal(β1-4)[Fuc(α1-3)]GlcNAc(β1-2)Man(α1-"], [], [], false⟩
  | .e385C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/38.html", "2-Carb-38.5/385C",
        ["(c) short form", "Galβ-4(Fucα-3)GlcNAcβ-2Manα-",
          "Galβ4(Fucα3)GlcNAcβ2Manα-",
          "recommended as the most explicit representation of branching using the short form"],
        [], [], false⟩
  | .e392 =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.2/392",
        ["An L-arabinan", "more specifically an α-L-arabinan"], [], [], false⟩
  | .e393A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.3/393A",
        ["(2→1)-β-D-Fructofuranan"], [], ["inulin"], false⟩
  | .e393B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.3/393B",
        ["Poly[(β-D-ribofuranosyl-5-O-yl)(1-deoxy-D-ribitol-1-C,5-O-diyl)" ++
          "(oxidophosphoryl)]",
          "[5)-β-D-Ribf-(1→1)-D-Rib-ol-5-P-(O→]ₙ"], [], [], false⟩
  | .e394 =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.4/394",
        ["Gellan (a bacterial polysaccharide originally designated S-60)"], [], ["gellan"], false⟩
  | .e395 =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.5/395",
        ["(1→4)-α-D-galacturonan"], [], ["pectin component"], false⟩
  | .e397A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.7/397A",
        ["A D-galacto-D-mannan"], [], ["guaran"], false⟩
  | .e397B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.7/397B",
        ["A less branched D-galacto-D-mannan shown in the short form"], [], [], false⟩
  | .e397C =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.7/397C",
        ["Xanthan"], [], ["xanthan"], false⟩
  | .e398A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.8/398A",
        ["(4-O-Methyl-α-D-glucurono)-D-xylan"], [], [], false⟩
  | .e398B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.8/398B",
        ["2,3-Di-O-acetyl-6-O-tritylamylose"], [], [], false⟩
  | .e399A =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.9/399A",
        ["Poly-[(3,6-Di-O-methyl-β-D-glucopyranosyl)-(1→4)-" ++
          "(2,3-di-O-methyl-α-L-rhamnopyranosyl)-(1→2)-" ++
          "(3-O-methyl-α-L-rhamnopyranosyloxy)-(1-O→9)-nonanoyl-(1→N)]-protein",
          "{[β-D-Glcp3,6Me₂-(1→4)-α-L-Rhap2,3Me₂-(1→2)-" ++
            "α-L-Rhap3Me-(1-O→9)-nonanoyl-(1→N)]ₙ-protein}"], [], [], false⟩
  | .e399B =>
      ⟨"https://iupac.qmul.ac.uk/2carb/39.html", "2-Carb-39.9/399B",
        ["Poly-[(3,6-Di-O-methyl-β-D-glucopyranosyl)-(1→4)-" ++
          "(2,3-di-O-methyl-α-L-rhamnopyranosyl)-(1→2)-" ++
          "(3-O-methyl-α-L-rhamnopyranosyloxy)-(1-O→4′)-" ++
          "(3-phenylpropanoyl)-(1→Nᴸʸˢ)]-protein"], [], [], false⟩

@[simp] theorem PrintedExample.data_sourceKey_exact (row : PrintedExample) :
    row.data.sourceKey = row.sourceKey := by
  cases row <;> rfl

theorem PrintedExample.data_text_nonempty (row : PrintedExample) :
    row.data.acceptedText ≠ [] ∨ row.data.discouragedText ≠ [] ∨ row.data.trivialNames ≠ [] := by
  cases row <;> simp [PrintedExample.data]

@[simp] theorem PrintedExample.data_figureGraphTranscribed_false (row : PrintedExample) :
    row.data.figureGraphTranscribed = false := by
  cases row <;> rfl

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map PrintedExample.sourceKey).Nodup := by decide

theorem PrintedExample.data_sourceKeys_nodup :
    (PrintedExample.all.map fun row => row.data.sourceKey).Nodup := by
  simpa only [PrintedExample.data_sourceKey_exact] using printed_example_keys_are_pairwise_distinct

inductive DisaccharideTrivialRow where
  | cellobiose | gentiobiose | isomaltose | melibiose | primeverose | rutinose
  deriving DecidableEq, Repr

namespace DisaccharideTrivialRow

def all : List DisaccharideTrivialRow :=
  [ .cellobiose, .gentiobiose, .isomaltose, .melibiose, .primeverose, .rutinose ]

@[simp] theorem mem_all (row : DisaccharideTrivialRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem length_all : all.length = 6 := by decide

end DisaccharideTrivialRow

structure DisaccharideTrivialData where
  commonName : String
  preferredSystematicName : String
  alternativeSystematicName : String
  deriving DecidableEq, Repr

def DisaccharideTrivialRow.data : DisaccharideTrivialRow → DisaccharideTrivialData
  | .cellobiose =>
      ⟨"Cellobiose", "β-D-Glucopyranosyl-(1→4)-D-glucose",
        "4-O-β-D-Glucopyranosyl-D-glucose"⟩
  | .gentiobiose =>
      ⟨"Gentiobiose", "β-D-Glucopyranosyl-(1→6)-D-glucose",
        "6-O-β-D-Glucopyranosyl-D-glucose"⟩
  | .isomaltose =>
      ⟨"Isomaltose", "α-D-Glucopyranosyl-(1→6)-D-glucose",
        "6-O-α-D-Glucopyranosyl-D-glucose"⟩
  | .melibiose =>
      ⟨"Melibiose", "α-D-Galactopyranosyl-(1→6)-D-glucose",
        "6-O-α-D-galactopyranosyl-D-glucose"⟩
  | .primeverose =>
      ⟨"Primeverose", "β-D-Xylopyranosyl-(1→6)-D-glucose",
        "6-O-β-D-xylopyranosyl-D-glucose"⟩
  | .rutinose =>
      ⟨"Rutinose", "α-L-Rhamnopyranosyl-(1→6)-D-glucose",
        "6-O-α-L-rhamnopyranosyl-D-glucose"⟩

def DisaccharideTrivialRow.sourceKey (row : DisaccharideTrivialRow) : String :=
  "2-Carb-36.4/Table-6/" ++ row.data.commonName

theorem disaccharide_trivial_names_are_pairwise_distinct :
    (DisaccharideTrivialRow.all.map fun row => row.data.commonName).Nodup := by decide

inductive SymbolRow where
  | abequose | iduronicAcid | allose | lyxose | altrose | mannose | apiose | muramicAcid
  | arabinose | neuraminicAcid | arabinitol | nAcetylneuraminicAcid | twoDeoxyribose
  | nAcetylTwoDeoxyNeurTwoEnaminicAcid | fructose | nGlycoloylneuraminicAcid | fucose
  | kdo | fucitol | rhamnose | galactose | diOMethylrhamnose | galactosamine | psicose
  | nAcetylgalactosamine | quinovose | betaDGalactopyranoseFourSulfate | ribose | glucose
  | riboseFivePhosphate | glucosamine | ribulose | diaminoDideoxyGlucose | sorbose | glucitol
  | tagatose | nAcetylglucosamine | talose | glucuronicAcid | xylose
  | ethylGlucopyranuronate | xylulose | gulose | twoCMethylxylose | idose
  deriving DecidableEq, Repr

namespace SymbolRow

def all : List SymbolRow :=
  [ .abequose, .iduronicAcid, .allose, .lyxose, .altrose, .mannose, .apiose
  , .muramicAcid, .arabinose, .neuraminicAcid, .arabinitol, .nAcetylneuraminicAcid
  , .twoDeoxyribose, .nAcetylTwoDeoxyNeurTwoEnaminicAcid, .fructose
  , .nGlycoloylneuraminicAcid, .fucose, .kdo, .fucitol, .rhamnose, .galactose
  , .diOMethylrhamnose, .galactosamine, .psicose, .nAcetylgalactosamine, .quinovose
  , .betaDGalactopyranoseFourSulfate, .ribose, .glucose, .riboseFivePhosphate
  , .glucosamine, .ribulose, .diaminoDideoxyGlucose, .sorbose, .glucitol, .tagatose
  , .nAcetylglucosamine, .talose, .glucuronicAcid, .xylose, .ethylGlucopyranuronate
  , .xylulose, .gulose, .twoCMethylxylose, .idose
  ]

@[simp] theorem mem_all (row : SymbolRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem length_all : all.length = 45 := by decide

end SymbolRow

structure SymbolData where
  residueName : String
  primarySymbol : String
  alternativeSymbol? : Option String := none
  deriving DecidableEq, Repr

def SymbolRow.data : SymbolRow → SymbolData
  | .abequose => ⟨"Abequose", "Abe", none⟩
  | .iduronicAcid => ⟨"Iduronic acid", "IdoA", none⟩
  | .allose => ⟨"Allose", "All", none⟩
  | .lyxose => ⟨"Lyxose", "Lyx", none⟩
  | .altrose => ⟨"Altrose", "Alt", none⟩
  | .mannose => ⟨"Mannose", "Man", none⟩
  | .apiose => ⟨"Apiose", "Api", none⟩
  | .muramicAcid => ⟨"Muramic acid", "Mur", none⟩
  | .arabinose => ⟨"Arabinose", "Ara", none⟩
  | .neuraminicAcid => ⟨"Neuraminic acid", "Neu", none⟩
  | .arabinitol => ⟨"Arabinitol", "Ara-ol", none⟩
  | .nAcetylneuraminicAcid => ⟨"N-Acetylneuraminic acid", "Neu5Ac", none⟩
  | .twoDeoxyribose => ⟨"2-Deoxyribose", "dRib", none⟩
  | .nAcetylTwoDeoxyNeurTwoEnaminicAcid =>
      ⟨"N-Acetyl-2-deoxyneur-2-enaminic acid", "Neu2en5Ac", none⟩
  | .fructose => ⟨"Fructose", "Fru", none⟩
  | .nGlycoloylneuraminicAcid => ⟨"N-Glycoloylneuraminic acid", "Neu5Gc", none⟩
  | .fucose => ⟨"Fucose", "Fuc", none⟩
  | .kdo => ⟨"3-Deoxy-D-manno-oct-2-ulosonic acid", "Kdo", none⟩
  | .fucitol => ⟨"Fucitol", "Fuc-ol", none⟩
  | .rhamnose => ⟨"Rhamnose", "Rha", none⟩
  | .galactose => ⟨"Galactose", "Gal", none⟩
  | .diOMethylrhamnose => ⟨"3,4-Di-O-methylrhamnose", "Rha3,4Me2", none⟩
  | .galactosamine => ⟨"Galactosamine", "GalN", none⟩
  | .psicose => ⟨"Psicose", "Psi", none⟩
  | .nAcetylgalactosamine => ⟨"N-Acetylgalactosamine", "GalNAc", none⟩
  | .quinovose => ⟨"Quinovose", "Qui", none⟩
  | .betaDGalactopyranoseFourSulfate =>
      ⟨"β-D-Galactopyranose 4-sulfate", "β-D-Galp4S", none⟩
  | .ribose => ⟨"Ribose", "Rib", none⟩
  | .glucose => ⟨"Glucose", "Glc", none⟩
  | .riboseFivePhosphate => ⟨"Ribose 5-phosphate", "Rib5P", none⟩
  | .glucosamine => ⟨"Glucosamine", "GlcN", none⟩
  | .ribulose => ⟨"Ribulose", "Ribulo", some "Rul"⟩
  | .diaminoDideoxyGlucose =>
      ⟨"2,3-Diamino-2,3-dideoxy-D-glucose", "GlcN3N", none⟩
  | .sorbose => ⟨"Sorbose", "Sor", none⟩
  | .glucitol => ⟨"Glucitol", "Glc-ol", none⟩
  | .tagatose => ⟨"Tagatose", "Tag", none⟩
  | .nAcetylglucosamine => ⟨"N-Acetylglucosamine", "GlcNAc", none⟩
  | .talose => ⟨"Talose", "Tal", none⟩
  | .glucuronicAcid => ⟨"Glucuronic acid", "GlcA", none⟩
  | .xylose => ⟨"Xylose", "Xyl", none⟩
  | .ethylGlucopyranuronate => ⟨"Ethyl glucopyranuronate", "GlcpA6Et", none⟩
  | .xylulose => ⟨"Xylulose", "Xylulo", some "Xul"⟩
  | .gulose => ⟨"Gulose", "Gul", none⟩
  | .twoCMethylxylose => ⟨"2-C-Methylxylose", "Xyl2CMe", none⟩
  | .idose => ⟨"Idose", "Ido", none⟩

def SymbolRow.sourceKey (row : SymbolRow) : String :=
  "2-Carb-38.1/Table-2/" ++ row.data.residueName

theorem primary_symbols_are_pairwise_distinct :
    (SymbolRow.all.map fun row => row.data.primarySymbol).Nodup := by decide

inductive Provision where
  | disaccharideTwoMonosaccharidesJoinedByGlycosidicLinkage
  | nonreducingTwoAnomericHydroxylReaction
  | nonreducingNameGlycosylGlycoside
  | nonreducingParentByCarb21
  | nonreducingBothAnomericDescriptorsRequired
  | nonreducingTerm
  | nonreducingTrivialDerivativeFirstSystematicComponentPrimed
  | reducingOneGlycosylReplacesAlcoholicHydroxylHydrogen
  | reducingNameGlycosylglycose
  | reducingLinkageLocantsRequired
  | reducingAnomericDescriptorsRequired
  | reducingTwoEstablishedLocantMethods
  | reducingParentheticalLocantsPreferred
  | reducingPrefixLocantsCAS
  | previousOLocantsOmitted
  | reducingTerm
  | establishedDisaccharideTrivialNames
  | earlierTrehaloseSucroseMaltoseLactoseSystematicNames
  | reducingTrivialDerivativeFirstSystematicComponentPrimed
  | uronicEsterGlycosideEsterAlkylAtBeginning
  | uronicEsterGlycosideAglyconicAlkylWithResidue
  | nonfreeHigherOligosaccharideNameForms
  | nonfreeGlycosidePortionChoiceByCarb21
  | nonfreeSequentialMethodRegardlessOfCarb21
  | nonfreePreferredDisaccharideLocantMethod
  | interResidueSyntaxAnomericLocantArrowOxygenLocant
  | trivialDerivativeLastComponentUnprimedThenReversePrimes
  | higherDerivativeSystematicNamingPreferred
  | freeOligosaccharideGlycosylNGlycose
  | reducingSugarIsParent
  | freeOligosaccharideDescriptorsAndLocants
  | conventionalReducingResidueRight
  | conventionalNonreducingResidueLeft
  | internalUnitsAreGlycosylResidues
  | anhydrosugarUnitTermDiscouraged
  | downstreamEndGeneralTerm
  | higherOligosaccharidesSameSystematicMethod
  | higherOligosaccharideSymbolsOftenPreferable
  | maltoSeriesTrivialNames
  | otherHomoOligosaccharideNamesSparing
  | residueRomanNumeralsAscendingFromReducingEnd
  | residueArabicNumeralsCanConflict
  | residueRomanNumeralsFollowGlycolipidUsage
  | branchTermsInSquareBrackets
  | branchedLongestChainIsParent
  | equalLengthLowerBranchLocantPreferred
  | traditionalBranchDepictionMayDiffer
  | cyclicSemisystematicCycloLinkageCountOse
  | cyclodextrinTrivialNamesEstablished
  | nonOneFourCyclicLinkagesSystematic
  | schardingerAndCyclohexaamyloseNamesNotRecommended
  | cdAbbreviationTolerated
  | uniformCyclicSubstitutionSingleMultiplicativePrefix
  | varyingCyclicSubstitutionUsesRomanResidueLocants
  | cyclicSystematicCycloMultiplicativeLinkageResidue
  | oneSixCyclicNameNotCycloisomaltohexaose
  | methyleneLinkReplacementUsesCarba
  | methyleneReplacementLocantFromLowerRomanResidue
  | methyleneReplacementLocantHasSuperscriptRomanAndA
  | oxyaminoLinkReplacementUsesAminoSugarNomenclature
  | symbolsRecommendedForLongCarbohydrateSequences
  | symbolsWithLocantsAndAnomersAdequatelyDescribeSequences
  | commonResidueSymbolsListedInTableTwo
  | symbolsGenerallyDerivedFromTrivialNames
  | substituentAbbreviationsFollowResidueSymbolDirectly
  | substituentAbbreviationsPrecededByLocants
  | reducingOrModifiedReducingResidueAtRight
  | noncarbohydrateLinkedGlycosylResidueAtRight
  | residueNumberingRightToLeft
  | extendedFormCarbBankAndPreferred
  | extendedSymbolPrecededByAnomericDescriptor
  | extendedSymbolPrecededByConfiguration
  | extendedRingSizeExplicit
  | extendedLinkLocantsParenthesized
  | extendedDoubleArrowForTwoAnomericPositions
  | extendedOmittedAnomerMeansUnknown
  | extendedOmittedConfigurationMeansUnknown
  | extendedOmittedRingSizeMeansUnknown
  | extendedBranchesSecondLineOrBrackets
  | extendedHyphensOptionalExceptConfigurationSeparation
  | condensedConfigurationAndRingOmitted
  | condensedDefaultConfigurationD
  | condensedFucoseAndIduronicUsuallyL
  | condensedDefaultRingPyranose
  | condensedAnomerInsideLinkageParentheses
  | abbreviatedExtendedUsuallyPreferShortForm
  | shortOmitAnomericCarbonLocants
  | shortOmitLinkageParentheses
  | shortHyphensOptional
  | shortBranchesUseEnclosingMarks
  | shortMayRestoreConfigurationAndRingDetail
  | shortExplicitBranchingVersionRecommended
  | symbolicMainChainMayDeviateFromCarb373
  | symbolicDeviationSupportsHomomorphicRelationships
  | homoglycanSingleResidueType
  | homoglycanOseEndingBecomesAn
  | establishedXylanMannanGalactanUsage
  | celluloseAndStarchAreGlucans
  | knownResidueSeriesMayPrefixGlycanName
  | majorHomoglycanLinkageMayBeNamed
  | linkageDesignationNamesBondedCarbons
  | linkagePrecedesConfigurationSymbols
  | nonglycosidicPolymerGlycanTerminologyInappropriate
  | nonglycosidicPolymerUsesPolymerNomenclature
  | broadCurrentPracticeMayStillClassifyAsPolysaccharide
  | newPolysaccharideNamesEndAn
  | anNameMeansUnsubstitutedPolysaccharide
  | establishedPolysaccharideNamesRetained
  | carrageenanAndLaminaranCurrentUsage
  | glycuronicAcidIcAcidEndingBecomesAn
  | glycuronanGenericName
  | polyuronideTermIncorrect
  | aminoPolysaccharideModifiesSystematicAminoSugarName
  | heteroglycanHasAtLeastTwoResidueKinds
  | singleTypeBackboneCitedLastAsGlycan
  | nonbackboneResiduesAlphabeticalGlycoPrefixes
  | noPrincipalChainAllResiduesAlphabeticalGlycoPrefixes
  | noPrincipalChainNameEndsGlycan
  | substitutedGlycanCitesEverySubstituentType
  | substitutedGlycanSubstituentsAlphabetical
  | carbohydrateAminoAcidPolymersUseThreeBroadTerms
  | broadConjugateTermsHaveNoPreciseBoundary
  | glycoproteinHasLowMassCarbohydrateGroups
  | proteoglycanHasHighMassPolysaccharide
  | peptidoglycanHasPolysaccharideAndPeptideChains
  | conjugateNomenclatureDelegated
  | neoglycoproteinForSyntheticOrModifiedConjugate
  | conjugateCarbohydrateSubstituentUsesSequentialOligosaccharideNaming
  | disaccharideTrivialRow (row : DisaccharideTrivialRow)
  | symbolRow (row : SymbolRow)
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .disaccharideTwoMonosaccharidesJoinedByGlycosidicLinkage
  , .nonreducingTwoAnomericHydroxylReaction, .nonreducingNameGlycosylGlycoside
  , .nonreducingParentByCarb21, .nonreducingBothAnomericDescriptorsRequired
  , .nonreducingTerm, .nonreducingTrivialDerivativeFirstSystematicComponentPrimed
  , .reducingOneGlycosylReplacesAlcoholicHydroxylHydrogen, .reducingNameGlycosylglycose
  , .reducingLinkageLocantsRequired, .reducingAnomericDescriptorsRequired
  , .reducingTwoEstablishedLocantMethods, .reducingParentheticalLocantsPreferred
  , .reducingPrefixLocantsCAS, .previousOLocantsOmitted, .reducingTerm
  , .establishedDisaccharideTrivialNames
  , .earlierTrehaloseSucroseMaltoseLactoseSystematicNames
  , .reducingTrivialDerivativeFirstSystematicComponentPrimed
  , .uronicEsterGlycosideEsterAlkylAtBeginning
  , .uronicEsterGlycosideAglyconicAlkylWithResidue
  , .nonfreeHigherOligosaccharideNameForms, .nonfreeGlycosidePortionChoiceByCarb21
  , .nonfreeSequentialMethodRegardlessOfCarb21, .nonfreePreferredDisaccharideLocantMethod
  , .interResidueSyntaxAnomericLocantArrowOxygenLocant
  , .trivialDerivativeLastComponentUnprimedThenReversePrimes
  , .higherDerivativeSystematicNamingPreferred, .freeOligosaccharideGlycosylNGlycose
  , .reducingSugarIsParent, .freeOligosaccharideDescriptorsAndLocants
  , .conventionalReducingResidueRight, .conventionalNonreducingResidueLeft
  , .internalUnitsAreGlycosylResidues, .anhydrosugarUnitTermDiscouraged
  , .downstreamEndGeneralTerm, .higherOligosaccharidesSameSystematicMethod
  , .higherOligosaccharideSymbolsOftenPreferable, .maltoSeriesTrivialNames
  , .otherHomoOligosaccharideNamesSparing, .residueRomanNumeralsAscendingFromReducingEnd
  , .residueArabicNumeralsCanConflict, .residueRomanNumeralsFollowGlycolipidUsage
  , .branchTermsInSquareBrackets, .branchedLongestChainIsParent
  , .equalLengthLowerBranchLocantPreferred, .traditionalBranchDepictionMayDiffer
  , .cyclicSemisystematicCycloLinkageCountOse, .cyclodextrinTrivialNamesEstablished
  , .nonOneFourCyclicLinkagesSystematic
  , .schardingerAndCyclohexaamyloseNamesNotRecommended, .cdAbbreviationTolerated
  , .uniformCyclicSubstitutionSingleMultiplicativePrefix
  , .varyingCyclicSubstitutionUsesRomanResidueLocants
  , .cyclicSystematicCycloMultiplicativeLinkageResidue
  , .oneSixCyclicNameNotCycloisomaltohexaose, .methyleneLinkReplacementUsesCarba
  , .methyleneReplacementLocantFromLowerRomanResidue
  , .methyleneReplacementLocantHasSuperscriptRomanAndA
  , .oxyaminoLinkReplacementUsesAminoSugarNomenclature
  , .symbolsRecommendedForLongCarbohydrateSequences
  , .symbolsWithLocantsAndAnomersAdequatelyDescribeSequences
  , .commonResidueSymbolsListedInTableTwo, .symbolsGenerallyDerivedFromTrivialNames
  , .substituentAbbreviationsFollowResidueSymbolDirectly
  , .substituentAbbreviationsPrecededByLocants, .reducingOrModifiedReducingResidueAtRight
  , .noncarbohydrateLinkedGlycosylResidueAtRight, .residueNumberingRightToLeft
  , .extendedFormCarbBankAndPreferred, .extendedSymbolPrecededByAnomericDescriptor
  , .extendedSymbolPrecededByConfiguration, .extendedRingSizeExplicit
  , .extendedLinkLocantsParenthesized, .extendedDoubleArrowForTwoAnomericPositions
  , .extendedOmittedAnomerMeansUnknown, .extendedOmittedConfigurationMeansUnknown
  , .extendedOmittedRingSizeMeansUnknown, .extendedBranchesSecondLineOrBrackets
  , .extendedHyphensOptionalExceptConfigurationSeparation
  , .condensedConfigurationAndRingOmitted, .condensedDefaultConfigurationD
  , .condensedFucoseAndIduronicUsuallyL, .condensedDefaultRingPyranose
  , .condensedAnomerInsideLinkageParentheses, .abbreviatedExtendedUsuallyPreferShortForm
  , .shortOmitAnomericCarbonLocants, .shortOmitLinkageParentheses, .shortHyphensOptional
  , .shortBranchesUseEnclosingMarks, .shortMayRestoreConfigurationAndRingDetail
  , .shortExplicitBranchingVersionRecommended, .symbolicMainChainMayDeviateFromCarb373
  , .symbolicDeviationSupportsHomomorphicRelationships, .homoglycanSingleResidueType
  , .homoglycanOseEndingBecomesAn, .establishedXylanMannanGalactanUsage
  , .celluloseAndStarchAreGlucans, .knownResidueSeriesMayPrefixGlycanName
  , .majorHomoglycanLinkageMayBeNamed, .linkageDesignationNamesBondedCarbons
  , .linkagePrecedesConfigurationSymbols
  , .nonglycosidicPolymerGlycanTerminologyInappropriate
  , .nonglycosidicPolymerUsesPolymerNomenclature
  , .broadCurrentPracticeMayStillClassifyAsPolysaccharide, .newPolysaccharideNamesEndAn
  , .anNameMeansUnsubstitutedPolysaccharide, .establishedPolysaccharideNamesRetained
  , .carrageenanAndLaminaranCurrentUsage, .glycuronicAcidIcAcidEndingBecomesAn
  , .glycuronanGenericName, .polyuronideTermIncorrect
  , .aminoPolysaccharideModifiesSystematicAminoSugarName
  , .heteroglycanHasAtLeastTwoResidueKinds, .singleTypeBackboneCitedLastAsGlycan
  , .nonbackboneResiduesAlphabeticalGlycoPrefixes
  , .noPrincipalChainAllResiduesAlphabeticalGlycoPrefixes, .noPrincipalChainNameEndsGlycan
  , .substitutedGlycanCitesEverySubstituentType, .substitutedGlycanSubstituentsAlphabetical
  , .carbohydrateAminoAcidPolymersUseThreeBroadTerms
  , .broadConjugateTermsHaveNoPreciseBoundary, .glycoproteinHasLowMassCarbohydrateGroups
  , .proteoglycanHasHighMassPolysaccharide, .peptidoglycanHasPolysaccharideAndPeptideChains
  , .conjugateNomenclatureDelegated, .neoglycoproteinForSyntheticOrModifiedConjugate
  , .conjugateCarbohydrateSubstituentUsesSequentialOligosaccharideNaming
  ]

def all : List Provision :=
  ((base ++ DisaccharideTrivialRow.all.map Provision.disaccharideTrivialRow) ++
    SymbolRow.all.map Provision.symbolRow) ++ PrintedExample.all.map Provision.printedExample

set_option maxHeartbeats 1000000 in
@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | disaccharideTrivialRow row =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.disaccharideTrivialRow) row.mem_all
  | symbolRow row =>
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.symbolRow) row.mem_all
  | printedExample exampleRow =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by
  have trivialRowsNodup :
      (DisaccharideTrivialRow.all.map Provision.disaccharideTrivialRow).Nodup :=
    DisaccharideTrivialRow.all_nodup.map (by intro left right equal; cases equal; rfl)
  have symbolRowsNodup : (SymbolRow.all.map Provision.symbolRow).Nodup :=
    SymbolRow.all_nodup.map (by intro left right equal; cases equal; rfl)
  have examplesNodup : (PrintedExample.all.map Provision.printedExample).Nodup :=
    PrintedExample.all_nodup.map (by intro left right equal; cases equal; rfl)
  simp [all, List.nodup_append', List.disjoint_left, base,
    trivialRowsNodup, symbolRowsNodup, examplesNodup]

@[simp] theorem length_all : all.length = 220 := by
  simp [all, base]

end Provision

def Provision.sourceKey : Provision → String
  | .disaccharideTwoMonosaccharidesJoinedByGlycosidicLinkage => "2-Carb-36.1"
  | .nonreducingTwoAnomericHydroxylReaction | .nonreducingNameGlycosylGlycoside
  | .nonreducingParentByCarb21 | .nonreducingBothAnomericDescriptorsRequired
  | .nonreducingTerm | .nonreducingTrivialDerivativeFirstSystematicComponentPrimed =>
      "2-Carb-36.2"
  | .reducingOneGlycosylReplacesAlcoholicHydroxylHydrogen | .reducingNameGlycosylglycose
  | .reducingLinkageLocantsRequired | .reducingAnomericDescriptorsRequired
  | .reducingTwoEstablishedLocantMethods | .reducingParentheticalLocantsPreferred
  | .reducingPrefixLocantsCAS | .previousOLocantsOmitted | .reducingTerm => "2-Carb-36.3"
  | .establishedDisaccharideTrivialNames
  | .earlierTrehaloseSucroseMaltoseLactoseSystematicNames
  | .reducingTrivialDerivativeFirstSystematicComponentPrimed
  | .uronicEsterGlycosideEsterAlkylAtBeginning
  | .uronicEsterGlycosideAglyconicAlkylWithResidue => "2-Carb-36.4"
  | .nonfreeHigherOligosaccharideNameForms | .nonfreeGlycosidePortionChoiceByCarb21
  | .nonfreeSequentialMethodRegardlessOfCarb21 | .nonfreePreferredDisaccharideLocantMethod
  | .interResidueSyntaxAnomericLocantArrowOxygenLocant
  | .trivialDerivativeLastComponentUnprimedThenReversePrimes
  | .higherDerivativeSystematicNamingPreferred => "2-Carb-37.1"
  | .freeOligosaccharideGlycosylNGlycose | .reducingSugarIsParent
  | .freeOligosaccharideDescriptorsAndLocants | .conventionalReducingResidueRight
  | .conventionalNonreducingResidueLeft | .internalUnitsAreGlycosylResidues
  | .anhydrosugarUnitTermDiscouraged | .downstreamEndGeneralTerm
  | .higherOligosaccharidesSameSystematicMethod | .higherOligosaccharideSymbolsOftenPreferable
  | .maltoSeriesTrivialNames | .otherHomoOligosaccharideNamesSparing
  | .residueRomanNumeralsAscendingFromReducingEnd | .residueArabicNumeralsCanConflict
  | .residueRomanNumeralsFollowGlycolipidUsage => "2-Carb-37.2"
  | .branchTermsInSquareBrackets | .branchedLongestChainIsParent
  | .equalLengthLowerBranchLocantPreferred | .traditionalBranchDepictionMayDiffer =>
      "2-Carb-37.3"
  | .cyclicSemisystematicCycloLinkageCountOse | .cyclodextrinTrivialNamesEstablished
  | .nonOneFourCyclicLinkagesSystematic
  | .schardingerAndCyclohexaamyloseNamesNotRecommended | .cdAbbreviationTolerated
  | .uniformCyclicSubstitutionSingleMultiplicativePrefix
  | .varyingCyclicSubstitutionUsesRomanResidueLocants => "2-Carb-37.4.1"
  | .cyclicSystematicCycloMultiplicativeLinkageResidue
  | .oneSixCyclicNameNotCycloisomaltohexaose => "2-Carb-37.4.2"
  | .methyleneLinkReplacementUsesCarba | .methyleneReplacementLocantFromLowerRomanResidue
  | .methyleneReplacementLocantHasSuperscriptRomanAndA
  | .oxyaminoLinkReplacementUsesAminoSugarNomenclature => "2-Carb-37.5"
  | .symbolsRecommendedForLongCarbohydrateSequences
  | .symbolsWithLocantsAndAnomersAdequatelyDescribeSequences
  | .commonResidueSymbolsListedInTableTwo | .symbolsGenerallyDerivedFromTrivialNames
  | .substituentAbbreviationsFollowResidueSymbolDirectly
  | .substituentAbbreviationsPrecededByLocants => "2-Carb-38.1"
  | .reducingOrModifiedReducingResidueAtRight
  | .noncarbohydrateLinkedGlycosylResidueAtRight | .residueNumberingRightToLeft =>
      "2-Carb-38.2"
  | .extendedFormCarbBankAndPreferred | .extendedSymbolPrecededByAnomericDescriptor
  | .extendedSymbolPrecededByConfiguration | .extendedRingSizeExplicit
  | .extendedLinkLocantsParenthesized | .extendedDoubleArrowForTwoAnomericPositions
  | .extendedOmittedAnomerMeansUnknown | .extendedOmittedConfigurationMeansUnknown
  | .extendedOmittedRingSizeMeansUnknown | .extendedBranchesSecondLineOrBrackets
  | .extendedHyphensOptionalExceptConfigurationSeparation => "2-Carb-38.3"
  | .condensedConfigurationAndRingOmitted | .condensedDefaultConfigurationD
  | .condensedFucoseAndIduronicUsuallyL | .condensedDefaultRingPyranose
  | .condensedAnomerInsideLinkageParentheses | .abbreviatedExtendedUsuallyPreferShortForm =>
      "2-Carb-38.4"
  | .shortOmitAnomericCarbonLocants | .shortOmitLinkageParentheses | .shortHyphensOptional
  | .shortBranchesUseEnclosingMarks | .shortMayRestoreConfigurationAndRingDetail
  | .shortExplicitBranchingVersionRecommended | .symbolicMainChainMayDeviateFromCarb373
  | .symbolicDeviationSupportsHomomorphicRelationships => "2-Carb-38.5"
  | .homoglycanSingleResidueType | .homoglycanOseEndingBecomesAn
  | .establishedXylanMannanGalactanUsage | .celluloseAndStarchAreGlucans => "2-Carb-39.1"
  | .knownResidueSeriesMayPrefixGlycanName => "2-Carb-39.2"
  | .majorHomoglycanLinkageMayBeNamed | .linkageDesignationNamesBondedCarbons
  | .linkagePrecedesConfigurationSymbols | .nonglycosidicPolymerGlycanTerminologyInappropriate
  | .nonglycosidicPolymerUsesPolymerNomenclature
  | .broadCurrentPracticeMayStillClassifyAsPolysaccharide => "2-Carb-39.3"
  | .newPolysaccharideNamesEndAn | .anNameMeansUnsubstitutedPolysaccharide
  | .establishedPolysaccharideNamesRetained | .carrageenanAndLaminaranCurrentUsage =>
      "2-Carb-39.4"
  | .glycuronicAcidIcAcidEndingBecomesAn | .glycuronanGenericName
  | .polyuronideTermIncorrect => "2-Carb-39.5"
  | .aminoPolysaccharideModifiesSystematicAminoSugarName => "2-Carb-39.6"
  | .heteroglycanHasAtLeastTwoResidueKinds | .singleTypeBackboneCitedLastAsGlycan
  | .nonbackboneResiduesAlphabeticalGlycoPrefixes
  | .noPrincipalChainAllResiduesAlphabeticalGlycoPrefixes
  | .noPrincipalChainNameEndsGlycan => "2-Carb-39.7"
  | .substitutedGlycanCitesEverySubstituentType
  | .substitutedGlycanSubstituentsAlphabetical => "2-Carb-39.8"
  | .carbohydrateAminoAcidPolymersUseThreeBroadTerms
  | .broadConjugateTermsHaveNoPreciseBoundary | .glycoproteinHasLowMassCarbohydrateGroups
  | .proteoglycanHasHighMassPolysaccharide | .peptidoglycanHasPolysaccharideAndPeptideChains
  | .conjugateNomenclatureDelegated | .neoglycoproteinForSyntheticOrModifiedConjugate
  | .conjugateCarbohydrateSubstituentUsesSequentialOligosaccharideNaming => "2-Carb-39.9"
  | .disaccharideTrivialRow row => row.sourceKey
  | .symbolRow row => row.sourceKey
  | .printedExample exampleRow => exampleRow.sourceKey

/-! ## Executable semantic consequences -/

inductive HemiacetalStatus where | free | unavailable
  deriving DecidableEq, Repr

inductive DisaccharideNameForm where | glycosylglycose | glycosylGlycoside
  deriving DecidableEq, Repr

def disaccharideNameForm : HemiacetalStatus → DisaccharideNameForm
  | .free => .glycosylglycose
  | .unavailable => .glycosylGlycoside

def requiredAnomericDescriptorCount : HemiacetalStatus → Nat
  | .free => 1
  | .unavailable => 2

@[simp] theorem nonreducing_disaccharide_requires_glycoside_form_and_two_anomers :
    disaccharideNameForm .unavailable = .glycosylGlycoside ∧
      requiredAnomericDescriptorCount .unavailable = 2 := by decide

@[simp] theorem reducing_disaccharide_routes_to_glycose_parent :
    disaccharideNameForm .free = .glycosylglycose := by rfl

inductive ChainEnd where | left | right
  deriving DecidableEq, Repr

def conventionalReducingEnd : ChainEnd := .right
def conventionalNonreducingEnd : ChainEnd := .left

@[simp] theorem conventional_chain_orientation :
    conventionalReducingEnd = .right ∧ conventionalNonreducingEnd = .left := by decide

structure ChainCandidate where
  residueCount : Nat
  branchLocant : Nat
  deriving DecidableEq, Repr

/-- 2-Carb-37.3: maximize length, then minimize the branch-point locant. -/
def preferredBranchChain (first second : ChainCandidate) : ChainCandidate :=
  if second.residueCount < first.residueCount then first
  else if first.residueCount < second.residueCount then second
  else if first.branchLocant ≤ second.branchLocant then first else second

theorem preferredBranchChain_of_longer_first (first second : ChainCandidate)
    (h : second.residueCount < first.residueCount) :
    preferredBranchChain first second = first := by simp [preferredBranchChain, h]

theorem preferredBranchChain_of_equal_length_lower_first_locant (first second : ChainCandidate)
    (hLength : first.residueCount = second.residueCount)
    (hLocant : first.branchLocant ≤ second.branchLocant) :
    preferredBranchChain first second = first := by
  simp [preferredBranchChain, hLength, hLocant]

inductive CyclicNameStyle where | semisystematicAllowed | systematicRequired
  deriving DecidableEq, Repr

def cyclicNameStyle (acceptorLocant : Nat) : CyclicNameStyle :=
  if acceptorLocant = 4 then .semisystematicAllowed else .systematicRequired

@[simp] theorem one_four_cyclic_linkage_allows_semisystematic_name :
    cyclicNameStyle 4 = .semisystematicAllowed := by decide

theorem non_one_four_cyclic_linkage_requires_systematic_name (locant : Nat)
    (h : locant ≠ 4) : cyclicNameStyle locant = .systematicRequired := by
  simp [cyclicNameStyle, h]

inductive LinkReplacement where | methylene | oxyamino
  deriving DecidableEq, Repr

inductive AnalogueNamingRoute where | carbaReplacement | aminoSugar
  deriving DecidableEq, Repr

def analogueNamingRoute : LinkReplacement → AnalogueNamingRoute
  | .methylene => .carbaReplacement
  | .oxyamino => .aminoSugar

@[simp] theorem oligosaccharide_link_replacement_routes :
    analogueNamingRoute .methylene = .carbaReplacement ∧
      analogueNamingRoute .oxyamino = .aminoSugar := by decide

inductive AbsoluteSeries where | D | L
  deriving DecidableEq, Repr

inductive RingSize where | furanose | pyranose
  deriving DecidableEq, Repr

structure CondensedDefaults where
  series : AbsoluteSeries
  ring : RingSize
  deriving DecidableEq, Repr

def condensedDefaults : SymbolRow → CondensedDefaults
  | .fucose | .iduronicAcid => ⟨.L, .pyranose⟩
  | _ => ⟨.D, .pyranose⟩

@[simp] theorem condensed_exception_defaults :
    condensedDefaults .fucose = ⟨.L, .pyranose⟩ ∧
      condensedDefaults .iduronicAcid = ⟨.L, .pyranose⟩ := by decide

theorem condensed_other_symbols_default_to_D_pyranose (row : SymbolRow)
    (hFuc : row ≠ .fucose) (hIdoA : row ≠ .iduronicAcid) :
    condensedDefaults row = ⟨.D, .pyranose⟩ := by
  cases row <;> simp_all [condensedDefaults]

structure ExtendedResidue where
  symbol : SymbolRow
  anomer? : Option Bool
  series? : Option AbsoluteSeries
  ring? : Option RingSize
  deriving DecidableEq, Repr

def structuralDetailKnown {α : Type} : Option α → Bool
  | some _ => true
  | none => false

@[simp] theorem extended_omission_means_unknown (symbol : SymbolRow) :
    let residue : ExtendedResidue := ⟨symbol, none, none, none⟩
    structuralDetailKnown residue.anomer? = false ∧
      structuralDetailKnown residue.series? = false ∧
      structuralDetailKnown residue.ring? = false := by simp [structuralDetailKnown]

inductive HeteroglycanNameRoute where
  | backboneLast
  | allGlycoPrefixesThenGlycan
  deriving DecidableEq, Repr

def heteroglycanNameRoute (hasSingleTypeBackbone : Bool) : HeteroglycanNameRoute :=
  if hasSingleTypeBackbone then .backboneLast else .allGlycoPrefixesThenGlycan

@[simp] theorem heteroglycan_parent_routes :
    heteroglycanNameRoute true = .backboneLast ∧
      heteroglycanNameRoute false = .allGlycoPrefixesThenGlycan := by decide

inductive ConjugateClass where | glycoprotein | proteoglycan | peptidoglycan
  deriving DecidableEq, Repr

inductive CarbohydrateComponent where | oligosaccharide | lowMassPolysaccharide | highMassPolysaccharide
  deriving DecidableEq, Repr

def conjugateClass (component : CarbohydrateComponent) (hasPeptideChains : Bool) : ConjugateClass :=
  if hasPeptideChains then .peptidoglycan
  else match component with
    | .highMassPolysaccharide => .proteoglycan
    | _ => .glycoprotein

@[simp] theorem conjugate_classification_examples :
    conjugateClass .oligosaccharide false = .glycoprotein ∧
      conjugateClass .highMassPolysaccharide false = .proteoglycan ∧
      conjugateClass .lowMassPolysaccharide true = .peptidoglycan := by decide

end Carbohydrate1996OligosaccharidesPolysaccharides
end TetraStereo.OneCenter
