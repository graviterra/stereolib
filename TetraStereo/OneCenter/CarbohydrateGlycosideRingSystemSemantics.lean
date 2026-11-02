import TetraStereo.OneCenter.CarbohydrateResidueIonStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent glycoside and additional-ring carbohydrate semantics

This module audits 2-Carb-33 through 2-Carb-35.  It enumerates every numbered example and
formalizes the stereochemical boundaries for extended glycosidic link atoms, replacement of ring
oxygen, fusion junctions, and spiro junctions.
-/

namespace Carbohydrate1996GlycosidesRings

inductive PrintedExample where
  | e331
  | e332A | e332B | e332C | e332D | e332E | e332F | e332G | e332H | e332I
  | e333A | e333B | e333C | e333D
  | e334A | e334B
  | e335A | e335B | e335C | e335D | e335E
  | e336A | e336B | e336C | e336D | e336E | e336F
  | e337A | e337B | e337C | e337D | e337E | e337F | e337G
  | e341A | e341B | e341C | e341D | e341E
  | e342A | e342B | e342C | e342D
  | e351A | e351B | e351C | e351D | e351E | e351F | e351G | e351H
  | e352A | e352B | e352C | e352D
  | e353A | e353B | e353C
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .e331
  , .e332A, .e332B, .e332C, .e332D, .e332E, .e332F, .e332G, .e332H, .e332I
  , .e333A, .e333B, .e333C, .e333D, .e334A, .e334B
  , .e335A, .e335B, .e335C, .e335D, .e335E
  , .e336A, .e336B, .e336C, .e336D, .e336E, .e336F
  , .e337A, .e337B, .e337C, .e337D, .e337E, .e337F, .e337G
  , .e341A, .e341B, .e341C, .e341D, .e341E
  , .e342A, .e342B, .e342C, .e342D
  , .e351A, .e351B, .e351C, .e351D, .e351E, .e351F, .e351G, .e351H
  , .e352A, .e352B, .e352C, .e352D, .e353A, .e353B, .e353C
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem length_all : all.length = 58 := by decide

end PrintedExample

def PrintedExample.sourceKey : PrintedExample → String
  | .e331 => "2-Carb-33.1/331"
  | .e332A => "2-Carb-33.2/332A" | .e332B => "2-Carb-33.2/332B"
  | .e332C => "2-Carb-33.2/332C" | .e332D => "2-Carb-33.2/332D"
  | .e332E => "2-Carb-33.2/332E" | .e332F => "2-Carb-33.2/332F"
  | .e332G => "2-Carb-33.2/332G" | .e332H => "2-Carb-33.2/332H"
  | .e332I => "2-Carb-33.2/332I"
  | .e333A => "2-Carb-33.3/333A" | .e333B => "2-Carb-33.3/333B"
  | .e333C => "2-Carb-33.3/333C" | .e333D => "2-Carb-33.3/333D"
  | .e334A => "2-Carb-33.4/334A" | .e334B => "2-Carb-33.4/334B"
  | .e335A => "2-Carb-33.5/335A" | .e335B => "2-Carb-33.5/335B"
  | .e335C => "2-Carb-33.5/335C" | .e335D => "2-Carb-33.5/335D"
  | .e335E => "2-Carb-33.5/335E"
  | .e336A => "2-Carb-33.6/336A" | .e336B => "2-Carb-33.6/336B"
  | .e336C => "2-Carb-33.6/336C" | .e336D => "2-Carb-33.6/336D"
  | .e336E => "2-Carb-33.6/336E" | .e336F => "2-Carb-33.6/336F"
  | .e337A => "2-Carb-33.7/337A" | .e337B => "2-Carb-33.7/337B"
  | .e337C => "2-Carb-33.7/337C" | .e337D => "2-Carb-33.7/337D"
  | .e337E => "2-Carb-33.7/337E" | .e337F => "2-Carb-33.7/337F"
  | .e337G => "2-Carb-33.7/337G"
  | .e341A => "2-Carb-34.1/341A" | .e341B => "2-Carb-34.1/341B"
  | .e341C => "2-Carb-34.1/341C" | .e341D => "2-Carb-34.1/341D"
  | .e341E => "2-Carb-34.1/341E"
  | .e342A => "2-Carb-34.2/342A" | .e342B => "2-Carb-34.2/342B"
  | .e342C => "2-Carb-34.2/342C" | .e342D => "2-Carb-34.2/342D"
  | .e351A => "2-Carb-35.1/351A" | .e351B => "2-Carb-35.1/351B"
  | .e351C => "2-Carb-35.1/351C" | .e351D => "2-Carb-35.1/351D"
  | .e351E => "2-Carb-35.1/351E" | .e351F => "2-Carb-35.1/351F"
  | .e351G => "2-Carb-35.1/351G" | .e351H => "2-Carb-35.1/351H"
  | .e352A => "2-Carb-35.2/352A" | .e352B => "2-Carb-35.2/352B"
  | .e352C => "2-Carb-35.2/352C" | .e352D => "2-Carb-35.2/352D"
  | .e353A => "2-Carb-35.3/353A" | .e353B => "2-Carb-35.3/353B"
  | .e353C => "2-Carb-35.3/353C"

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map PrintedExample.sourceKey).Nodup := by decide

/-! ## Source-faithful printed-example transcription

The official 2-Carb-33--35 pages pair each displayed molecular figure with one or more printed
names. These records transcribe that nomenclature layer only. The figures themselves remain in
the separately hashed carbohydrate image inventory, so `figureGraphTranscribed` is deliberately
false for every row.
-/

structure PrintedExampleData where
  sourceURL : String
  sourceKey : String
  acceptedNames : List String
  discouragedNames : List String
  trivialNames : List String
  figureGraphTranscribed : Bool
  deriving DecidableEq, Repr

private def printedExampleData
    (sourceURL sourceKey : String)
    (acceptedNames : List String)
    (discouragedNames : List String := [])
    (trivialNames : List String := []) : PrintedExampleData :=
  ⟨sourceURL, sourceKey, acceptedNames, discouragedNames, trivialNames, false⟩

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .e331 => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.1/331" ["Methyl α-D-glucopyranoside"]
  | .e332A => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332A" ["Methyl α-D-gulofuranoside"] ["Methyl-α-D-gulofuranoside"]
  | .e332B => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332B" ["Ethyl β-D-fructopyranoside"]
  | .e332C => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332C" ["Methyl (6R)-D-gluco-hexodialdo-6,2-pyranoside"]
  | .e332D => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332D"
      [ "(20S)-20-Hydroxy-5β-pregnan-3α-yl β-D-glucopyranosiduronic acid"
      , "(20S)-3α-(β-D-glucopyranosyloxyuronic acid)-5β-pregnan-20-ol" ] []
      ["pregnanediol 3-glucuronide"]
  | .e332E => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332E"
      [ "4-Acetylphenyl β-D-glucopyranoside"
      , "4'-(β-D-glucopyranosyloxy)acetophenone" ] [] ["picein"]
  | .e332F => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332F"
      [ "(S)-O-β-D-Glucopyranosylmandelonitrile"
      , "(S)-(β-D-glucopyranosyloxy)(phenyl)acetonitrile" ] [] ["sambunigrin"]
  | .e332G => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332G" ["7-(β-D-Glucopyranosyloxy)-8-hydroxycoumarin"] [] ["daphnin"]
  | .e332H => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332H" ["O³-β-D-Xylopyranosyl-L-serine [(Xyl-)Ser]"]
  | .e332I => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.2/332I"
      ["(Methyl 5-deoxy-β-D-xylofuranosid-5-yl) 2-(4-hydroxy-3-methoxyphenyl)-7-methoxy-5-[2-(methyl β-D-xylofuranosid-5-O-ylcarbonyl)vinyl]-2,3-dihydrobenzofuran-3-carboxylate"]
  | .e333A => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.3/333A" ["Ethyl 1-thio-β-D-glucopyranoside"]
  | .e333B => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.3/333B"
      [ "4-(α-D-Ribofuranosylthio)benzoic acid"
      , "4-Carboxyphenyl 1-thio-α-D-ribofuranoside" ]
  | .e333C => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.3/333C"
      ["S-β-D-Glucopyranosyl (Z)-O-(potassium sulfonato)but-3-enehydroximothioate"] []
      ["sinigrin"]
  | .e333D => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.3/333D"
      [ "Phenyl tetra-O-acetyl-α-D-glucopyranosyl sulfoxide"
      , "Phenyl 2,3,4,6-tetra-O-acetyl-1-thio-α-D-glucopyranoside S-oxide" ]
  | .e334A => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.4/334A"
      [ "2-Carboxyethyl 1-seleno-β-D-xylopyranoside"
      , "3-(β-D-Xylopyranosylseleno)propanoic acid" ]
  | .e334B => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.4/334B"
      [ "Se-β-D-Ribopyranosyl-D-selenocysteine"
      , "(S)-2-Amino-2-carboxyethyl 1-seleno-β-D-ribopyranoside"
      , "3-(β-D-Ribopyranosylseleno)-D-alanine" ]
  | .e335A => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.5/335A" ["Tetra-O-acetyl-α-D-mannopyranosyl bromide"]
  | .e335B => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.5/335B"
      ["Methyl (2,3,4-tri-O-acetyl-α-D-glucopyranosyl)uronate bromide"]
      ["Methyl 2,3,4-tri-O-acetyl-1-bromo-1-deoxy-α-D-glucopyranuronate"]
  | .e335C => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.5/335C" ["3,4,6-Tri-O-benzyl-α-D-arabino-hexopyranosyl-2-ulose bromide"]
  | .e335D => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.5/335D"
      [ "3,4,5-Tri-O-benzyl-α-D-arabino-hexos-2-ulo-2,6-pyranosyl bromide"
      , "3,4,5-Tri-O-benzyl-aldehydo-α-D-arabino-hexos-2-ulopyranosyl bromide" ]
  | .e335E => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.5/335E"
      ["Methyl (5-acetamido-4,7,8,9-tetra-O-acetyl-3,5-dideoxy-D-glycero-α-D-galacto-non-2-ulopyranosyl)onate chloride"]
  | .e336A => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.6/336A" ["N-Phenyl-α-D-fructopyranosylamine"]
      ["Aniline α-D-fructopyranoside"]
  | .e336B => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.6/336B" ["1-β-D-Ribofuranosyluracil"] [] ["uridine"]
  | .e336C => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.6/336C"
      ["N¹-(2-Acetamido-2-deoxy-β-D-glucopyranosyl)-L-lysinamide [(GlcNAc-)Lys]"] []
      ["N¹-(N-acetylglucosaminyl)-L-lysinamide"]
  | .e336D => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.6/336D" ["9-(5-S-Methyl-5-thio-β-D-ribofuranosyl)adenine"]
  | .e336E => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.6/336E"
      [ "N⁴-(2-Acetamido-2-deoxy-β-D-glucopyranosyl)-L-asparagine [(GlcNAc-)Asn]"
      , "2-Acetamido-N¹-L-β-aspartyl-2-deoxy-β-D-glucopyranosylamine" ] []
      ["β-N-acetylglucosaminyl-L-asparagine"]
  | .e336F => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.6/336F" ["Bis(α-D-glucopyranosyluronamide)amine"]
  | .e337A => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337A" ["4-β-D-Glucopyranosylbenzoic acid"]
      ["4-Carboxyphenyl C-β-D-glucopyranoside"]
  | .e337B => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337B" ["8-(2-Deoxy-β-D-erythro-pentofuranosyl)adenine"]
      ["Adenine 8-(2-deoxyriboside)"]
  | .e337C => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337C" ["5-β-D-Ribofuranosyluracil"] [] ["pseudouridine"]
  | .e337D => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337D"
      [ "3,7-Anhydro-2-deoxy-D-glycero-D-gulo-octononitrile"
      , "2-C-(β-D-Glucopyranosyl)acetonitrile" ]
      ["Cyanomethyl C-β-D-glucopyranoside"]
  | .e337E => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337E" ["2-β-D-Glucopyranosyl-1,3,6,7-tetrahydroxyxanthen-9-one"] []
      ["mangiferin"]
  | .e337F => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337F"
      ["(10S)-10-β-D-Glucopyranosyl-1,8-dihydroxy-3-(hydroxymethyl)anthracen-9(10H)-one"] []
      ["aloin A", "(10S)-barbaloin"]
  | .e337G => printedExampleData "https://iupac.qmul.ac.uk/2carb/33.html"
      "2-Carb-33.7/337G"
      ["6-β-D-Glucopyranosyl-4',5,7-trihydroxy-8-α-L-rhamnopyranosylflavone"] []
      ["violanthin"]
  | .e341A => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.1/341A" ["5-Amino-5-deoxy-D-glucopyranose"] [] ["nojirimycin"]
  | .e341B => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.1/341B"
      [ "1-Amino-1,5-anhydro-1-deoxy-D-mannitol"
      , "1,5-Dideoxy-1,5-imino-D-mannitol" ] [] ["deoxymannojirimycin"]
  | .e341C => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.1/341C" ["5-Deoxy-5-ethylamino-α-D-glucopyranose"]
  | .e341D => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.1/341D" ["5-Deoxy-5-phosphanyl-D-xylopyranose"]
  | .e341E => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.1/341E" ["Methyl 3-deoxy-3-aza-α-D-ribo-hexopyranoside"]
  | .e342A => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.2/342A" ["5a-Carba-β-D-glucopyranose"]
  | .e342B => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.2/342B"
      ["1-(2-Deoxy-4a-carba-β-D-erythro-pentofuranosyl)thymine", "4'a-Carbathymidine"]
  | .e342C => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.2/342C" ["5a-Carba-β-D-fructofuranosyl 5a-carba-α-D-glucopyranoside"]
  | .e342D => printedExampleData "https://iupac.qmul.ac.uk/2carb/34.html"
      "2-Carb-34.2/342D"
      [ "1-[(4aS)-2-Deoxy-4a-fluoro-4a-carba-β-D-erythro-pentofuranosyl]thymine"
      , "(4'aS)-4'a-Fluoro-4'a-carbathymidine" ]
  | .e351A => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351A"
      [ "2,3:4,5-Di-O-isopropylidene-β-D-fructopyranose"
      , "2,2,2',2'-Tetramethyl-4,4',5,5'-tetrahydro-(2,3,4,5-tetradeoxy-β-D-fructopyranoso)[2,3-d:4,5-d']bis[1,3]dioxole" ]
  | .e351B => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351B" ["Methyl [(S)-4,6-O-(1-methoxycarbonylethylidene)]-β-D-mannopyranoside"]
  | .e351C => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351C"
      [ "Methyl 2,3-(butane-1,4-diyl)-2,3-dideoxy-β-D-glucopyranoside"
      , "Hexahydro(methyl 2,3-dideoxy-β-D-glucopyranosido)[2,3]benzene" ]
  | .e351D => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351D"
      [ "Methyl 2,3-(buta-1,3-diene-1,4-diyl)-2,3-dideoxy-β-D-erythro-hex-2-enopyranoside"
      , "(Methyl 2,3-dideoxy-β-D-erythro-hexopyranosido)[2,3]benzene" ]
  | .e351E => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351E"
      ["1,6-Anhydro-2,3-dideoxy-2,3-(9,10-dihydroanthracene-9,10-diyl)-β-L-ribo-hexopyranos-4-ulose"]
  | .e351F => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351F"
      ["(1S)-1,5-Anhydro-3,4,6-tri-O-benzyl-1-C,2-O-(o-phenylenemethylene)-D-mannitol"]
  | .e351G => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351G"
      ["Methyl 4-N-acetyl-2,3-di-O-acetyl-4,6-diamino-4,6-N-cyclo-4,6-dideoxy-α-D-galactopyranoside"]
  | .e351H => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.1/351H"
      ["Methyl 2,3-di-O-acetyl-4,6-cyclo-4,6-dideoxy-β-D-galactopyranoside"]
  | .e352A => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.2/352A"
      [ "2-Phenyl-4,5-dihydro-(1,2-dideoxy-α-D-glucopyranoso)[2,1-d]-1,3-oxazole"
      , "2-Amino-1-O,2-N-(benzylylidene)-2-deoxy-α-D-glucopyranose" ]
  | .e352B => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.2/352B"
      [ "2-Methylamino-4,5-dihydro-(3,4,6-tri-O-acetyl-1,2-dideoxy-α-D-glucopyranoso)[2,1-d]-1,3-oxazole"
      , "3,4,6-Tri-O-acetyl-2-amino-2-deoxy-1-O,2-N-[(methylamino)methylylidene]-α-D-glucopyranose" ]
  | .e352C => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.2/352C"
      [ "3-Phenyltetrahydro-(1,2-dideoxy-α-D-glucopyranoso)[1,2-d]imidazol-2-one"
      , "2-Amino-1,2-N-carbonyl-1,2-dideoxy-1-N-phenyl-α-D-glucopyranosylamine" ]
  | .e352D => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.2/352D"
      [ "2-Methyl-5,6-dihydro-(4-O-acetyl-1,2,3,6-tetradeoxy-3-methyl-α-L-ribo-hexopyranoso)[3,2,1-de]-4H-1,3-oxazine"
      , "4-O-Acetyl-3-amino-2,3,6-trideoxy-1-O,3-N-(ethan-1-yl-1-yliene)-3-C-methyl-α-L-ribo-hexopyranose" ]
  | .e353A => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.3/353A"
      ["(1R)-2,3,4,6-Tetra-O-acetyl-3'-phenylspiro[1,5-anhydro-D-glucitol-1,5'-[1,4,2]oxathiazole]"]
  | .e353B => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.3/353B"
      ["(3S)-5-O-Benzoyl-1',2'-dihydro-1,2-O-isopropylidenespiro[3-deoxy-α-D-erythro-pentofuranose-3,3'-naphtho[1,2-e][1,3]oxazin]-2'-ol"]
  | .e353C => printedExampleData "https://iupac.qmul.ac.uk/2carb/35.html"
      "2-Carb-35.3/353C" ["Methyl 2,3-O-D-glucopyranosylidene-α-D-mannopyranoside"]

@[simp] theorem PrintedExample.data_sourceKey_exact (row : PrintedExample) :
    row.data.sourceKey = row.sourceKey := by
  cases row <;> rfl

theorem PrintedExample.data_acceptedNames_nonempty (row : PrintedExample) :
    row.data.acceptedNames ≠ [] := by
  cases row <;> simp [PrintedExample.data, printedExampleData]

@[simp] theorem PrintedExample.data_figureGraphTranscribed_false (row : PrintedExample) :
    row.data.figureGraphTranscribed = false := by
  cases row <;> rfl

theorem PrintedExample.data_sourceKeys_nodup :
    (PrintedExample.all.map fun row => row.data.sourceKey).Nodup := by
  simpa only [PrintedExample.data_sourceKey_exact] using
    printed_example_keys_are_pairwise_distinct

inductive Provision where
  | originalGlycosideDefinitionMixedCyclicAcetal
  | extendedGlycosidicReplacementAtoms
  | thioAndSelenoglycosideGenericTermsLegitimate
  | nGlycosideImproperPreferGlycosylamine
  | cGlycosideTerminologyLessAcceptable
  | aglyconeAndGlyconeTerms
  | glycosideThreeNamingMethods
  | classicalGlycosideEToIdeAndSeparateRWord
  | classicalMethodForSimpleR
  | glycosyloxyPrefixIncludesOxygen
  | oGlycosylPrefixExcludesOxygen
  | glycuronosylPracticeUnsatisfactory
  | glycosyloxyuronicTwoWordPrefixTradeoff
  | glycosideSubstituentsUseResidueMethods
  | thioglycosideThreeNamingMethods
  | glycosylthioIncludesSulfur
  | sGlycosylExcludesSulfur
  | thioglycosideOxidesUseFunctionalClass
  | selenoglycosidesAnalogousToThioglycosides
  | glycosylHalideDefinition
  | glycosylPseudohalidesAnalogous
  | nGlycosylDerivativesPreferGlycosylamine
  | complexHeterocyclicAminesUseSameMethod
  | cLinkedFormalWaterEliminationUsesGlycosylPrefix
  | cLinkedNamesAvoidCGlycoside
  | cGlycosideMisnomerStronglyDiscouraged
  | ringNitrogenPhosphorusUsesAminoPhosphanylSugarParent
  | heteroRingSizeDesignatorsMatchOxygenAnalogues
  | anhydroExtendedToAminoHydroxyWaterLoss
  | azaPhosphaReservedForCarbonReplacement
  | iminoSugarClassNameAllowed
  | carbaIsNondetachableRingOxygenReplacement
  | carbaLocantUsesNonanomericAdjacentAtomPlusA
  | carbaLocantDiffersFromDraftNaturalProductRule
  | newCarbaCarbonAdditionalStereochemistryUsesRS
  | carbaStructuresMayAlsoUseCyclitolNames
  | bridgeNamingHasPrefixAndFusionApproaches
  | bridgeRecommendationsProvisional
  | heteroatomBridgePrefixMeansTwoHeteroSubstitutions
  | externalBridgeHeteroatomsBelongToBridge
  | carbonBridgeMeansDoubleCSubstitution
  | ylideneBridgePrefixTraditionalButGenerallyDeprecated
  | cycloPrefixMayNameSingleBondBridge
  | fusionCarbohydrateFirstParenthesizedAndEToO
  | newFusionRingBondsEquivalentToHydroxy
  | carbohydrateSubstituentsInsideFusionParentheses
  | newRingSubstituentsPrecedeCarbohydrateTerm
  | newRingNumberingFollowsFusionLocants
  | carbohydrateFirstOverridesGeneralFusionOrdering
  | pyranosoRecommendedOverPyrano
  | spiroUsesGeneralProcedures
  | spiroJunctionPrefixesAdjacentToCarbohydrateStem
  | spiroCarbohydrateComponentCitedFirst
  | spiroJunctionConfigurationUsesRS
  | spiroDisaccharidePrefersGemBivalentPrefix
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision
def base : List Provision :=
  [ .originalGlycosideDefinitionMixedCyclicAcetal, .extendedGlycosidicReplacementAtoms
  , .thioAndSelenoglycosideGenericTermsLegitimate, .nGlycosideImproperPreferGlycosylamine
  , .cGlycosideTerminologyLessAcceptable, .aglyconeAndGlyconeTerms
  , .glycosideThreeNamingMethods, .classicalGlycosideEToIdeAndSeparateRWord
  , .classicalMethodForSimpleR, .glycosyloxyPrefixIncludesOxygen
  , .oGlycosylPrefixExcludesOxygen, .glycuronosylPracticeUnsatisfactory
  , .glycosyloxyuronicTwoWordPrefixTradeoff, .glycosideSubstituentsUseResidueMethods
  , .thioglycosideThreeNamingMethods, .glycosylthioIncludesSulfur, .sGlycosylExcludesSulfur
  , .thioglycosideOxidesUseFunctionalClass, .selenoglycosidesAnalogousToThioglycosides
  , .glycosylHalideDefinition, .glycosylPseudohalidesAnalogous
  , .nGlycosylDerivativesPreferGlycosylamine, .complexHeterocyclicAminesUseSameMethod
  , .cLinkedFormalWaterEliminationUsesGlycosylPrefix, .cLinkedNamesAvoidCGlycoside
  , .cGlycosideMisnomerStronglyDiscouraged
  , .ringNitrogenPhosphorusUsesAminoPhosphanylSugarParent
  , .heteroRingSizeDesignatorsMatchOxygenAnalogues, .anhydroExtendedToAminoHydroxyWaterLoss
  , .azaPhosphaReservedForCarbonReplacement, .iminoSugarClassNameAllowed
  , .carbaIsNondetachableRingOxygenReplacement, .carbaLocantUsesNonanomericAdjacentAtomPlusA
  , .carbaLocantDiffersFromDraftNaturalProductRule
  , .newCarbaCarbonAdditionalStereochemistryUsesRS, .carbaStructuresMayAlsoUseCyclitolNames
  , .bridgeNamingHasPrefixAndFusionApproaches, .bridgeRecommendationsProvisional
  , .heteroatomBridgePrefixMeansTwoHeteroSubstitutions
  , .externalBridgeHeteroatomsBelongToBridge, .carbonBridgeMeansDoubleCSubstitution
  , .ylideneBridgePrefixTraditionalButGenerallyDeprecated, .cycloPrefixMayNameSingleBondBridge
  , .fusionCarbohydrateFirstParenthesizedAndEToO, .newFusionRingBondsEquivalentToHydroxy
  , .carbohydrateSubstituentsInsideFusionParentheses
  , .newRingSubstituentsPrecedeCarbohydrateTerm, .newRingNumberingFollowsFusionLocants
  , .carbohydrateFirstOverridesGeneralFusionOrdering, .pyranosoRecommendedOverPyrano
  , .spiroUsesGeneralProcedures, .spiroJunctionPrefixesAdjacentToCarbohydrateStem
  , .spiroCarbohydrateComponentCitedFirst, .spiroJunctionConfigurationUsesRS
  , .spiroDisaccharidePrefersGemBivalentPrefix
  ]

def all : List Provision := base ++ PrintedExample.all.map Provision.printedExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | printedExample exampleRow =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem length_all : all.length = 113 := by decide
end Provision

def Provision.sourceKey : Provision → String
  | .originalGlycosideDefinitionMixedCyclicAcetal | .extendedGlycosidicReplacementAtoms
  | .thioAndSelenoglycosideGenericTermsLegitimate | .nGlycosideImproperPreferGlycosylamine
  | .cGlycosideTerminologyLessAcceptable | .aglyconeAndGlyconeTerms => "2-Carb-33.1"
  | .glycosideThreeNamingMethods | .classicalGlycosideEToIdeAndSeparateRWord
  | .classicalMethodForSimpleR | .glycosyloxyPrefixIncludesOxygen
  | .oGlycosylPrefixExcludesOxygen | .glycuronosylPracticeUnsatisfactory
  | .glycosyloxyuronicTwoWordPrefixTradeoff | .glycosideSubstituentsUseResidueMethods => "2-Carb-33.2"
  | .thioglycosideThreeNamingMethods | .glycosylthioIncludesSulfur
  | .sGlycosylExcludesSulfur | .thioglycosideOxidesUseFunctionalClass => "2-Carb-33.3"
  | .selenoglycosidesAnalogousToThioglycosides => "2-Carb-33.4"
  | .glycosylHalideDefinition | .glycosylPseudohalidesAnalogous => "2-Carb-33.5"
  | .nGlycosylDerivativesPreferGlycosylamine
  | .complexHeterocyclicAminesUseSameMethod => "2-Carb-33.6"
  | .cLinkedFormalWaterEliminationUsesGlycosylPrefix | .cLinkedNamesAvoidCGlycoside
  | .cGlycosideMisnomerStronglyDiscouraged => "2-Carb-33.7"
  | .ringNitrogenPhosphorusUsesAminoPhosphanylSugarParent
  | .heteroRingSizeDesignatorsMatchOxygenAnalogues | .anhydroExtendedToAminoHydroxyWaterLoss
  | .azaPhosphaReservedForCarbonReplacement | .iminoSugarClassNameAllowed => "2-Carb-34.1"
  | .carbaIsNondetachableRingOxygenReplacement | .carbaLocantUsesNonanomericAdjacentAtomPlusA
  | .carbaLocantDiffersFromDraftNaturalProductRule | .newCarbaCarbonAdditionalStereochemistryUsesRS
  | .carbaStructuresMayAlsoUseCyclitolNames => "2-Carb-34.2"
  | .bridgeNamingHasPrefixAndFusionApproaches | .bridgeRecommendationsProvisional => "2-Carb-35"
  | .heteroatomBridgePrefixMeansTwoHeteroSubstitutions
  | .externalBridgeHeteroatomsBelongToBridge | .carbonBridgeMeansDoubleCSubstitution
  | .ylideneBridgePrefixTraditionalButGenerallyDeprecated
  | .cycloPrefixMayNameSingleBondBridge => "2-Carb-35.1"
  | .fusionCarbohydrateFirstParenthesizedAndEToO | .newFusionRingBondsEquivalentToHydroxy
  | .carbohydrateSubstituentsInsideFusionParentheses | .newRingSubstituentsPrecedeCarbohydrateTerm
  | .newRingNumberingFollowsFusionLocants | .carbohydrateFirstOverridesGeneralFusionOrdering
  | .pyranosoRecommendedOverPyrano => "2-Carb-35.2"
  | .spiroUsesGeneralProcedures | .spiroJunctionPrefixesAdjacentToCarbohydrateStem
  | .spiroCarbohydrateComponentCitedFirst | .spiroJunctionConfigurationUsesRS
  | .spiroDisaccharidePrefersGemBivalentPrefix => "2-Carb-35.3"
  | .printedExample exampleRow => exampleRow.sourceKey

inductive GlycosidicLinkAtom where | oxygen | sulfur | selenium | nitrogen | carbon
  deriving DecidableEq, Repr
inductive RecommendedTerm where
  | glycoside | thioglycoside | selenoglycoside | glycosylamine | cLinkedGlycosylCompound
  deriving DecidableEq, Repr

def recommendedTerm : GlycosidicLinkAtom → RecommendedTerm
  | .oxygen => .glycoside
  | .sulfur => .thioglycoside
  | .selenium => .selenoglycoside
  | .nitrogen => .glycosylamine
  | .carbon => .cLinkedGlycosylCompound

@[simp] theorem nitrogen_and_carbon_links_avoid_improper_glycoside_terms :
    recommendedTerm .nitrogen = .glycosylamine ∧
      recommendedTerm .carbon = .cLinkedGlycosylCompound := by decide

inductive NewRingCenter where | carbaCarbon | spiroJunction
  deriving DecidableEq, Repr
inductive DescriptorFamily where | CIPRS
  deriving DecidableEq, Repr
def descriptorForNewRingCenter (_ : NewRingCenter) : DescriptorFamily := .CIPRS

@[simp] theorem new_carba_and_spiro_centers_route_to_CIP_RS :
    descriptorForNewRingCenter .carbaCarbon = .CIPRS ∧
      descriptorForNewRingCenter .spiroJunction = .CIPRS := by decide

inductive FusionJunctionSurrogate where | hydroxy | retainedHydroxy
  deriving DecidableEq, Repr
def fusionJunctionSurrogate (hydroxyStillPresent : Bool) : FusionJunctionSurrogate :=
  if hydroxyStillPresent then .retainedHydroxy else .hydroxy

@[simp] theorem new_fusion_bond_is_hydroxy_equivalent_absent_retained_hydroxy :
    fusionJunctionSurrogate false = .hydroxy ∧
      fusionJunctionSurrogate true = .retainedHydroxy := by decide

end Carbohydrate1996GlycosidesRings
end TetraStereo.OneCenter
