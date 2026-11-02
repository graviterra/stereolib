import TetraStereo.OneCenter.CarbohydrateOligosaccharidePolysaccharideSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate appendix, errata, and glossary semantics

This module transcribes every nonblank row of the retained-name appendix, every published erratum,
and every cell and footnote of the glycose-term glossary accompanying the 1996 carbohydrate
recommendations.  The appendix explicitly calls its inventory non-limiting; exhaustiveness here
therefore means every printed row, not every carbohydrate trivial name that may exist.
-/

namespace Carbohydrate1996AppendixErrataGlossary

inductive AppendixCategory where
  | parentMonosaccharide
  | commonTrivialName
  | modifiedNonstandardParent
  deriving DecidableEq, Repr

structure RetainedNameData where
  category : AppendixCategory
  retainedName : String
  symbol? : Option String
  systematicEquivalent : String
  deriving DecidableEq, Repr

def retainedNameRows : List RetainedNameData :=
  [ ⟨.parentMonosaccharide, "Allose", some "All", "allo-Hexose"⟩
  , ⟨.parentMonosaccharide, "Altrose", some "Alt", "altro-Hexose"⟩
  , ⟨.parentMonosaccharide, "Arabinose", some "Ara", "arabino-Pentose"⟩
  , ⟨.parentMonosaccharide, "Erythrose", none, "erythro-Tetrose"⟩
  , ⟨.parentMonosaccharide, "Erythrulose", none, "glycero-Tetrulose"⟩
  , ⟨.parentMonosaccharide, "Fructose", some "Fru", "arabino-Hex-2-ulose"⟩
  , ⟨.parentMonosaccharide, "D-Fucitol", some "D-Fuc-ol", "6-Deoxy-D-galactitol"⟩
  , ⟨.parentMonosaccharide, "L-Fucitol", some "L-Fuc-ol", "1-Deoxy-D-galactitol"⟩
  , ⟨.parentMonosaccharide, "Fucosamine", some "FucN", "2-Amino-2,6-dideoxygalactose"⟩
  , ⟨.parentMonosaccharide, "Fucose", some "Fuc", "6-Deoxygalactose"⟩
  , ⟨.parentMonosaccharide, "Galactosamine", some "GalN", "2-Amino-2-deoxygalactose"⟩
  , ⟨.parentMonosaccharide, "D-Galactosaminitol", some "GalN-ol",
      "2-Amino-2-deoxy-D-galactitol"⟩
  , ⟨.parentMonosaccharide, "Galactose", some "Gal", "galacto-Hexose"⟩
  , ⟨.parentMonosaccharide, "Glucosamine", some "GlcN", "2-Amino-2-deoxyglucose"⟩
  , ⟨.parentMonosaccharide, "Glucosaminitol", some "GlcN-ol", "2-Amino-2-deoxyglucitol"⟩
  , ⟨.parentMonosaccharide, "Glucose", some "Glc", "gluco-Hexose"⟩
  , ⟨.parentMonosaccharide, "Glyceraldehyde", none, "2,3-Dihydroxypropanal"⟩
  , ⟨.parentMonosaccharide, "Glycerol", some "Gro", "Propane-1,2,3-triol"⟩
  , ⟨.parentMonosaccharide, "Glycerone (1,3-dihydroxyacetone)", none,
      "1,3-Dihydroxypropanone"⟩
  , ⟨.parentMonosaccharide, "Gulose", some "Gul", "gulo-Hexose"⟩
  , ⟨.parentMonosaccharide, "Idose", some "Ido", "ido-Hexose"⟩
  , ⟨.parentMonosaccharide, "Lyxose", some "Lyx", "lyxo-Pentose"⟩
  , ⟨.parentMonosaccharide, "Mannosamine", some "ManN", "2-Amino-2-deoxymannose"⟩
  , ⟨.parentMonosaccharide, "Mannose", some "Man", "manno-Hexose"⟩
  , ⟨.parentMonosaccharide, "Psicose", some "Psi", "ribo-Hex-2-ulose"⟩
  , ⟨.parentMonosaccharide, "Quinovose", some "Qui", "6-Deoxyglucose"⟩
  , ⟨.parentMonosaccharide, "Quinovosamine", none, "2-Amino-2,6-dideoxyglucose"⟩
  , ⟨.parentMonosaccharide, "Rhamnitol", some "Rha-ol", "1-Deoxymannitol"⟩
  , ⟨.parentMonosaccharide, "Rhamnosamine", some "RhaN", "2-Amino-2,6-dideoxymannose"⟩
  , ⟨.parentMonosaccharide, "Rhamnose", some "Rha", "6-Deoxymannose"⟩
  , ⟨.parentMonosaccharide, "Ribose", some "Rib", "ribo-Pentose"⟩
  , ⟨.parentMonosaccharide, "Ribulose", some "Rul", "erythro-Pent-2-ulose"⟩
  , ⟨.parentMonosaccharide, "Sorbose", some "Sor", "xylo-Hex-2-ulose"⟩
  , ⟨.parentMonosaccharide, "Tagatose", some "Tag", "lyxo-Hex-2-ulose"⟩
  , ⟨.parentMonosaccharide, "Talose", some "Tal", "talo-Hexose"⟩
  , ⟨.parentMonosaccharide, "Tartaric acid", none, "Erythraric/Threaric acid"⟩
  , ⟨.parentMonosaccharide, "Threose", none, "threo-Tetrose"⟩
  , ⟨.parentMonosaccharide, "Xylose", some "Xyl", "xylo-Pentose"⟩
  , ⟨.parentMonosaccharide, "Xylulose", some "Xul", "threo-Pent-2-ulose"⟩

  , ⟨.commonTrivialName, "Abequose", some "Abe", "3,6-Dideoxy-D-xylo-hexose"⟩
  , ⟨.commonTrivialName, "Amicetose", none, "2,3,6-Trideoxy-D-erythro-hexose"⟩
  , ⟨.commonTrivialName, "Amylose", none, "(1→4)-α-D-Glucopyranan"⟩
  , ⟨.commonTrivialName, "Apiose", some "Api", "3-C-(Hydroxymethyl)-glycero-tetrose"⟩
  , ⟨.commonTrivialName, "Arcanose", none,
      "2,6-Dideoxy-3-C-methyl-3-O-methyl-xylo-hexose"⟩
  , ⟨.commonTrivialName, "Ascarylose", none, "3,6-Dideoxy-L-arabino-hexose"⟩
  , ⟨.commonTrivialName, "Ascorbic acid", none, "L-threo-Hex-2-enono-1,4-lactone"⟩
  , ⟨.commonTrivialName, "Boivinose", none, "2,6-Dideoxy-D-gulose"⟩
  , ⟨.commonTrivialName, "Cellobiose", none,
      "β-D-Glucopyranosyl-(1→4)-D-glucose"⟩
  , ⟨.commonTrivialName, "Cellotriose", none,
      "β-D-Glucopyranosyl-(1→4)-β-D-glucopyranosyl-(1→4)-D-glucose"⟩
  , ⟨.commonTrivialName, "Chacotriose", none,
      "α-L-Rhamnopyranosyl-(1→2)-[α-L-rhamnopyranosyl-(1→4)]-D-glucose"⟩
  , ⟨.commonTrivialName, "Chalcose", none,
      "4,6-Dideoxy-3-O-methyl-D-xylo-hexose"⟩
  , ⟨.commonTrivialName, "Cladinose", none,
      "2,6-Dideoxy-3-C-methyl-3-O-methyl-L-ribo-hexose"⟩
  , ⟨.commonTrivialName, "Colitose", none, "3,6-Dideoxy-L-xylo-hexose"⟩
  , ⟨.commonTrivialName, "Cymarose", none, "2,6-Dideoxy-3-O-methyl-ribo-hexose"⟩
  , ⟨.commonTrivialName, "2-Deoxyribose", some "dRib", "2-Deoxy-erythro-pentose"⟩
  , ⟨.commonTrivialName, "2-Deoxyglucose", some "2dGlc", "2-Deoxy-arabino-hexose"⟩
  , ⟨.commonTrivialName, "Diginose", none, "2,6-Dideoxy-3-O-methyl-lyxo-hexose"⟩
  , ⟨.commonTrivialName, "Digitalose", none, "6-Deoxy-3-O-methyl-D-galactose"⟩
  , ⟨.commonTrivialName, "Digitoxose", none, "2,6-Dideoxy-D-ribo-hexose"⟩
  , ⟨.commonTrivialName, "Evalose", none, "6-Deoxy-3-C-methyl-D-mannose"⟩
  , ⟨.commonTrivialName, "Evernitrose", none,
      "2,3,6-Trideoxy-3-C-methyl-4-O-methyl-3-nitro-L-arabino-hexose"⟩
  , ⟨.commonTrivialName, "Gentianose", none,
      "β-D-Fructofuranosyl β-D-glucopyranosyl-(1→6)-α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Gentiobiose", none,
      "β-D-Glucopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Hamamelose", none, "2-C-(Hydroxymethyl)-D-ribose"⟩
  , ⟨.commonTrivialName, "Inulin", none, "(2→1)-β-D-Fructofuranan"⟩
  , ⟨.commonTrivialName, "Isolevoglucosenone", none,
      "1,6-Anhydro-2,3-dideoxy-β-D-glycero-hex-2-enoyranos-4-ulose"⟩
  , ⟨.commonTrivialName, "Isomaltose", none,
      "α-D-Glucopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Isomaltotriose", none,
      "α-D-Glucopyranosyl-(1→6)-α-D-glucopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Isopanose", none,
      "α-D-Glucopyranosyl-(1→4)-[α-D-glucopyranosyl-(1→6)]-D-glucose"⟩
  , ⟨.commonTrivialName, "Kojibiose", none,
      "α-D-Glucopyranosyl-(1→2)-D-glucose"⟩
  , ⟨.commonTrivialName, "Lactose", some "Lac",
      "β-D-Galactopyranosyl-(1→4)-D-glucose"⟩
  , ⟨.commonTrivialName, "Lactosamine", some "LacN",
      "β-D-Galactopyranosyl-(1→4)-D-glucosamine"⟩
  , ⟨.commonTrivialName, "Lactosediamine", some "LacdiN",
      "2-Amino-2-deoxy-β-D-galactopyranosyl-(1→4)-D-glucosamine"⟩
  , ⟨.commonTrivialName, "Laminarabiose", none,
      "β-D-Glucopyranosyl-(1→3)-D-glucose"⟩
  , ⟨.commonTrivialName, "Levoglucosan", none, "1,6-Anhydro-β-D-glucopyranose"⟩
  , ⟨.commonTrivialName, "Levoglucosenone", none,
      "1,6-Anhydro-3,4-dideoxy-β-D-glycero-hex-3-enoyranos-2-ulose"⟩
  , ⟨.commonTrivialName, "Maltose", none,
      "α-D-Glucopyranosyl-(1→4)-D-glucose"⟩
  , ⟨.commonTrivialName, "Manninotriose", none,
      "α-D-Galactopyranosyl-(1→6)-α-D-galactopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Melezitose", none,
      "α-D-Glucopyranosyl-(1→3)-β-D-fructofuranosyl α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Melibiose", none,
      "α-D-Galactopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Muramic acid", some "Mur",
      "2-Amino-3-O-[(R)-1-carboxyethyl]-2-deoxy-D-glucose"⟩
  , ⟨.commonTrivialName, "Mycarose", none, "2,6-Dideoxy-3-C-methyl-L-ribo-hexose"⟩
  , ⟨.commonTrivialName, "Mycinose", none, "6-Deoxy-2,3-di-O-methyl-D-allose"⟩
  , ⟨.commonTrivialName, "Neuraminic acid", some "Neu",
      "5-Amino-3,5-dideoxy-D-glycero-D-galacto-non-2-ulosonic acid"⟩
  , ⟨.commonTrivialName, "Nigerose", none,
      "α-D-Glucopyranosyl-(1→3)-D-glucose"⟩
  , ⟨.commonTrivialName, "Nojirimycin", none, "5-Amino-5-deoxy-D-glucopyranose"⟩
  , ⟨.commonTrivialName, "Noviose", none,
      "6-Deoxy-5-C-methyl-4-O-methyl-L-lyxo-hexose"⟩
  , ⟨.commonTrivialName, "Oleandrose", none,
      "2,6-Dideoxy-3-O-methyl-L-arabino-hexose"⟩
  , ⟨.commonTrivialName, "Panose", none,
      "α-D-Glucopyranosyl-(1→6)-α-D-glucopyranosyl-(1→4)-D-glucose"⟩
  , ⟨.commonTrivialName, "Paratose", none, "3,6-Dideoxy-D-ribo-hexose"⟩
  , ⟨.commonTrivialName, "Planteose", none,
      "α-D-Galactopyranosyl-(1→6)-β-D-fructofuranosyl α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Primeverose", none,
      "β-D-Xylopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Raffinose", none,
      "β-D-Fructofuranosyl α-D-galactopyranosyl-(1→6)-α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Rhodinose", none, "2,3,6-Trideoxy-L-threo-hexose"⟩
  , ⟨.commonTrivialName, "Rutinose", none,
      "α-L-Rhamnopyranosyl-(1→6)-D-glucose"⟩
  , ⟨.commonTrivialName, "Sarmentose", none,
      "2,6-Dideoxy-3-O-methyl-D-xylo-hexose"⟩
  , ⟨.commonTrivialName, "Sedoheptulose", none, "D-altro-Hept-2-ulose"⟩
  , ⟨.commonTrivialName, "Sedoheptulosan", none,
      "2,7-Anhydro-β-D-altro-hept-2-ulopyranose"⟩
  , ⟨.commonTrivialName, "Solatriose", none,
      "α-L-Rhamnopyranosyl-(1→2)-[β-D-glucopyranosyl-(1→3)]-D-galactose"⟩
  , ⟨.commonTrivialName, "Sophorose", none,
      "β-D-Glucopyranosyl-(1→2)-D-glucose"⟩
  , ⟨.commonTrivialName, "Stachyose", none,
      "β-D-Fructofuranosyl α-D-galactopyranosyl-(1→6)-α-D-galactopyranosyl-(1→6)-α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Streptose", none, "5-Deoxy-3-C-formyl-L-lyxose"⟩
  , ⟨.commonTrivialName, "Sucrose (saccharose)", none,
      "β-D-Fructofuranosyl α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "α,α-Trehalose", none,
      "α-D-Glucopyranosyl α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Trehalosamine", none,
      "2-Amino-2-deoxy-α-D-glucopyranosyl α-D-glucopyranoside"⟩
  , ⟨.commonTrivialName, "Turanose", none,
      "α-D-Glucopyranosyl-(1→3)-D-fructose"⟩
  , ⟨.commonTrivialName, "Tyvelose", some "Tyv", "3,6-Dideoxy-D-arabino-hexose"⟩
  , ⟨.commonTrivialName, "Umbelliferose", none,
      "β-D-Fructofuranosyl α-D-galactopyranosyl-(1→2)-α-D-glucopyranoside"⟩

  , ⟨.modifiedNonstandardParent, "Acosamine", none,
      "3-Amino-2,3,6-trideoxy-L-arabino-hexose"⟩
  , ⟨.modifiedNonstandardParent, "Bacillosamine", none,
      "2,4-Diamino-2,4,6-trideoxy-D-glucose"⟩
  , ⟨.modifiedNonstandardParent, "Daunosamine", none,
      "3-Amino-2,3,6-trideoxy-L-lyxo-hexose"⟩
  , ⟨.modifiedNonstandardParent, "Desosamine", none,
      "3,4,6-Trideoxy-3-dimethylamino-D-xylo-hexose"⟩
  , ⟨.modifiedNonstandardParent, "Forosamine", none,
      "2,3,4,6-Tetradeoxy-4-dimethylamino-D-erythro-hexose"⟩
  , ⟨.modifiedNonstandardParent, "Garosamine", none,
      "3-Deoxy-4-C-methyl-3-methylamino-L-arabinose"⟩
  , ⟨.modifiedNonstandardParent, "Kanosamine", none, "3-Amino-3-deoxy-D-glucose"⟩
  , ⟨.modifiedNonstandardParent, "Kansosamine", none,
      "4-Amino-4,6-dideoxy-3-C-methyl-2-O-methyl-L-mannose"⟩
  , ⟨.modifiedNonstandardParent, "Mycaminose", none,
      "3,6-Dideoxy-3-dimethylamino-D-glucose"⟩
  , ⟨.modifiedNonstandardParent, "Mycosamine", none,
      "3-Amino-3,6-dideoxy-D-mannose"⟩
  , ⟨.modifiedNonstandardParent, "Perosamine", none,
      "4-Amino-4,6-dideoxy-D-mannose"⟩
  , ⟨.modifiedNonstandardParent, "Pneumosamine", none,
      "2-Amino-2,6-dideoxy-D-talose"⟩
  , ⟨.modifiedNonstandardParent, "Purpurosamine C", none,
      "2,6-Diamino-2,3,4,6-tetradeoxy-D-erythro-hexose"⟩
  , ⟨.modifiedNonstandardParent, "Rhodosamine", none,
      "2,3,6-Trideoxy-3-dimethylamino-lyxo-hexose"⟩
  ]

@[simp] theorem retainedNameRows_length : retainedNameRows.length = 122 := by decide

abbrev RetainedNameRow := Fin retainedNameRows.length

namespace RetainedNameRow

def all : List RetainedNameRow := List.finRange retainedNameRows.length

@[simp] theorem mem_all (row : RetainedNameRow) : row ∈ all := by
  exact List.mem_finRange row
theorem all_nodup : all.Nodup := List.nodup_finRange retainedNameRows.length
@[simp] theorem length_all : all.length = 122 := by decide

def data (row : RetainedNameRow) : RetainedNameData := retainedNameRows.get row

end RetainedNameRow

theorem retained_name_and_category_keys_are_pairwise_distinct :
    (RetainedNameRow.all.map fun row => (row.data.category, row.data.retainedName)).Nodup := by
  set_option maxRecDepth 4096 in
    decide

structure ErratumData where
  target : String
  correction : String
  deriving DecidableEq, Repr

def errataRows : List ErratumData :=
  [ ⟨"2-Carb-5.4/example-6-third-from-end/right-structure",
      "Restore the omitted H of the C3 hydroxy group."⟩
  , ⟨"2-Carb-7.1/Chart-III/structure-11", "Restore the S linkage from C5 to C1."⟩
  , ⟨"2-Carb-12.1/last-example/left-version",
      "Restore H at C5; the name is Methyl α-L-xylo-hexos-2-ulo-2,5-furanoside."⟩
  , ⟨"2-Carb-16.3/example/first-name",
      "Use (2R)-2-Bromo-2-chloro-2-deoxy-α-D-arabino-hexopyranose."⟩
  , ⟨"2-Carb-16.5/last-example", "Delete the extra closing round bracket."⟩
  , ⟨"2-Carb-16.6/last-example", "Correct the name to indicate the pyranose ring."⟩
  , ⟨"2-Carb-17.2/sentence-2",
      "Add followed by 'o' for euphony before a consonant; use stereodescriptors, not stereosymbols."⟩
  , ⟨"2-Carb-18.5/side-chain-methylation", "Use side-chain-O-methylated."⟩
  , ⟨"2-Carb-22.2/example-4", "Restore the omitted OH at C3."⟩
  , ⟨"2-Carb-23.4/example-5", "The drawn structure is the D-isomer, not the L-isomer."⟩
  , ⟨"2-Carb-24.3/example-2/purine", "Restore the double bond common to both purine rings."⟩
  , ⟨"2-Carb-31.2/paragraphs-3-and-4", "Use 'a locant' rather than 'locants'."⟩
  , ⟨"2-Carb-31.2/example-12/second-name", "Correct the bracket in 1-(Adenin-9-yl)."⟩
  , ⟨"2-Carb-31.3/derivation-wording",
      "Replace terminal-e replacement wording by adding the suffix to the monosaccharide name."⟩
  , ⟨"2-Carb-33.6/example-3/abbreviation",
      "Show lysine bonded to C1 by drawing the glycosyl bond on the right-hand side."⟩
  , ⟨"2-Carb-37.2/paragraph-3", "Use (1→4)-linked rather than 1→4 linked."⟩
  , ⟨"References/18/Chemical-and-Engineering-News", "Use year 1953 for volume 31, page 1776."⟩
  , ⟨"References/21/Journal-of-Lipid-Research", "Use pages 114-128 for volume 19 (1978)."⟩
  , ⟨"Appendix-b/Cymarose", "Use 2,6-Dideoxy-3-O-methyl-ribo-hexose."⟩
  , ⟨"Appendix-b/Umbelliferose",
      "Use β-D-Fructofuranosyl α-D-galactopyranosyl-(1→2)-α-D-glucopyranoside."⟩
  , ⟨"Appendix-c/Acosamine", "Use 3-Amino-2,3,6-trideoxy-L-arabino-hexose."⟩
  , ⟨"Appendix-c/Kansosamine",
      "Use 4-Amino-4,6-dideoxy-3-C-methyl-2-O-methyl-L-mannose."⟩
  ]

@[simp] theorem errataRows_length : errataRows.length = 22 := by decide

abbrev ErratumRow := Fin errataRows.length

namespace ErratumRow

def all : List ErratumRow := List.finRange errataRows.length
@[simp] theorem mem_all (row : ErratumRow) : row ∈ all := by
  exact List.mem_finRange row
theorem all_nodup : all.Nodup := List.nodup_finRange errataRows.length
@[simp] theorem length_all : all.length = 22 := by decide
def data (row : ErratumRow) : ErratumData := errataRows.get row

end ErratumRow

theorem erratum_targets_are_pairwise_distinct :
    (ErratumRow.all.map fun row => row.data.target).Nodup := by decide

inductive GlossaryClass where
  | glycose | glycosyl | glycoside | glycosidase | glycosyltransferase
  deriving DecidableEq, Repr

inductive GlossaryFamily where
  | base | aminoSugar | uronicAcid | ulosonicAcid | sialicAcid
  deriving DecidableEq, Repr

structure GlossaryCellData where
  termClass : GlossaryClass
  family : GlossaryFamily
  standardTerms : List String
  biochemicalUsage : List String
  deriving DecidableEq, Repr

def glossaryCells : List GlossaryCellData :=
  [ ⟨.glycose, .base, ["Glycose"], []⟩
  , ⟨.glycose, .aminoSugar, ["Aminodeoxyglycose"], ["Glycosamine"]⟩
  , ⟨.glycose, .uronicAcid, ["Glycuronic acid", "Glycuronate"], []⟩
  , ⟨.glycose, .ulosonicAcid,
      ["Glyculosonic acid", "Glyculosonate"], ["Ketoglyconic acid"]⟩
  , ⟨.glycose, .sialicAcid, ["Neuraminic acid", "Sialic acid"], []⟩
  , ⟨.glycosyl, .base, ["Glycosyl"], []⟩
  , ⟨.glycosyl, .aminoSugar, ["Aminodeoxyglycosyl"], ["Glycosaminyl"]⟩
  , ⟨.glycosyl, .uronicAcid,
      ["Glycosyluronic acid", "Glycosyluronate"], ["Glycuronosyl"]⟩
  , ⟨.glycosyl, .ulosonicAcid, ["Glyculosylonic acid", "Glyculosylonate"], []⟩
  , ⟨.glycosyl, .sialicAcid, [], ["Neuraminosyl", "Sialosyl"]⟩
  , ⟨.glycoside, .base, ["Glycoside"], []⟩
  , ⟨.glycoside, .aminoSugar, ["Aminodeoxyglycoside"], ["Glycosaminide"]⟩
  , ⟨.glycoside, .uronicAcid,
      ["Glycosiduronic acid", "Glycosiduronate"], ["Glycuronide"]⟩
  , ⟨.glycoside, .ulosonicAcid, ["Glyculosidonic acid", "Glyculosidonate"], []⟩
  , ⟨.glycoside, .sialicAcid, [], ["Neuraminoside", "Sialoside"]⟩
  , ⟨.glycosidase, .base, ["Glycosidase", "Glycoside hydrolase"], []⟩
  , ⟨.glycosidase, .aminoSugar, ["Aminodeoxyglycosidase"], ["Glycosaminidase"]⟩
  , ⟨.glycosidase, .uronicAcid, ["Glycosiduronase"], ["Glycuronidase"]⟩
  , ⟨.glycosidase, .ulosonicAcid, ["Glyculosidonase"], []⟩
  , ⟨.glycosidase, .sialicAcid, [], ["Neuraminidase", "Sialidase"]⟩
  , ⟨.glycosyltransferase, .base, ["Glycosyltransferase"], []⟩
  , ⟨.glycosyltransferase, .aminoSugar,
      ["Aminodeoxyglycosyltransferase"], ["Glycosaminyltransferase"]⟩
  , ⟨.glycosyltransferase, .uronicAcid,
      ["Glycosyluronatetransferase"], ["Glycuronosyltransferase"]⟩
  , ⟨.glycosyltransferase, .ulosonicAcid, ["Glyculosylonatetransferase"], []⟩
  , ⟨.glycosyltransferase, .sialicAcid, [],
      ["Neuraminosyltransferase", "Sialosyltransferase"]⟩
  ]

@[simp] theorem glossaryCells_length : glossaryCells.length = 25 := by decide

abbrev GlossaryCell := Fin glossaryCells.length

namespace GlossaryCell

def all : List GlossaryCell := List.finRange glossaryCells.length
@[simp] theorem mem_all (cell : GlossaryCell) : cell ∈ all := by
  exact List.mem_finRange cell
theorem all_nodup : all.Nodup := List.nodup_finRange glossaryCells.length
@[simp] theorem length_all : all.length = 25 := by decide
def data (cell : GlossaryCell) : GlossaryCellData := glossaryCells.get cell

end GlossaryCell

theorem glossary_class_family_keys_are_pairwise_distinct :
    (GlossaryCell.all.map fun cell => (cell.data.termClass, cell.data.family)).Nodup := by
  decide

inductive GlossaryFootnote where | aminoUsageEstablished | impliedParentNames | avoidAcylAmbiguity
  deriving DecidableEq, Repr

namespace GlossaryFootnote

def all : List GlossaryFootnote :=
  [ .aminoUsageEstablished, .impliedParentNames, .avoidAcylAmbiguity ]
@[simp] theorem mem_all (footnote : GlossaryFootnote) : footnote ∈ all := by
  cases footnote <;> simp [all]
@[simp] theorem length_all : all.length = 3 := by decide

end GlossaryFootnote

def GlossaryFootnote.meaning : GlossaryFootnote → String
  | .aminoUsageEstablished => "The bracketed amino-sugar biochemical usage is widely established."
  | .impliedParentNames =>
      "The bracketed uronic/sialic biochemical usage implies glycuronose, sialose, and neuraminose parents."
  | .avoidAcylAmbiguity =>
      "Neuraminyl and sialyl risk interpretation as acyl groups; neuraminosyl and sialosyl are more consistent with glycoside terms."

inductive Provision where
  | appendixIsNonlimitingList
  | appendixGivesSystematicEquivalents
  | appendixGivesSymbolsWhereEstablished
  | retainedName (row : RetainedNameRow)
  | publishedErratum (row : ErratumRow)
  | glossaryCell (cell : GlossaryCell)
  | glossaryFootnote (footnote : GlossaryFootnote)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .appendixIsNonlimitingList, .appendixGivesSystematicEquivalents
  , .appendixGivesSymbolsWhereEstablished ]

def all : List Provision :=
  (((base ++ RetainedNameRow.all.map Provision.retainedName) ++
      ErratumRow.all.map Provision.publishedErratum) ++
    GlossaryCell.all.map Provision.glossaryCell) ++
    GlossaryFootnote.all.map Provision.glossaryFootnote

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | retainedName row =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.retainedName) row.mem_all
  | publishedErratum row =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.publishedErratum) row.mem_all
  | glossaryCell cell =>
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.glossaryCell) cell.mem_all
  | glossaryFootnote footnote =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.glossaryFootnote) footnote.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by
  have retainedNodup : (RetainedNameRow.all.map Provision.retainedName).Nodup :=
    RetainedNameRow.all_nodup.map (by intro left right equal; cases equal; rfl)
  have errataNodup : (ErratumRow.all.map Provision.publishedErratum).Nodup :=
    ErratumRow.all_nodup.map (by intro left right equal; cases equal; rfl)
  have glossaryNodup : (GlossaryCell.all.map Provision.glossaryCell).Nodup :=
    GlossaryCell.all_nodup.map (by intro left right equal; cases equal; rfl)
  have footnotesNodup : (GlossaryFootnote.all.map Provision.glossaryFootnote).Nodup := by
    decide
  simp [all, List.nodup_append', List.disjoint_left, base,
    retainedNodup, errataNodup, glossaryNodup, footnotesNodup]

@[simp] theorem length_all : all.length = 175 := by
  simp [all, base]

end Provision

def AppendixCategory.sourceKey : AppendixCategory → String
  | .parentMonosaccharide => "Appendix-a"
  | .commonTrivialName => "Appendix-b"
  | .modifiedNonstandardParent => "Appendix-c"

def GlossaryClass.sourceKey : GlossaryClass → String
  | .glycose => "GLOSA"
  | .glycosyl => "GLOSB"
  | .glycoside => "GLOSC"
  | .glycosidase => "GLOSD"
  | .glycosyltransferase => "GLOSE"

def GlossaryFamily.sourceKey : GlossaryFamily → String
  | .base => "base"
  | .aminoSugar => "amino-sugar"
  | .uronicAcid => "uronic-acid"
  | .ulosonicAcid => "ulosonic-acid"
  | .sialicAcid => "sialic-acid-family"

def GlossaryFootnote.sourceKey : GlossaryFootnote → String
  | .aminoUsageEstablished => "Glossary/footnote-a"
  | .impliedParentNames => "Glossary/footnote-b"
  | .avoidAcylAmbiguity => "Glossary/footnote-c"

def Provision.sourceKey : Provision → String
  | .appendixIsNonlimitingList | .appendixGivesSystematicEquivalents
  | .appendixGivesSymbolsWhereEstablished => "Appendix"
  | .retainedName row => row.data.category.sourceKey ++ "/" ++ row.data.retainedName
  | .publishedErratum row => "Errata/" ++ row.data.target
  | .glossaryCell cell =>
      "Glossary/" ++ cell.data.termClass.sourceKey ++ "/" ++ cell.data.family.sourceKey
  | .glossaryFootnote footnote => footnote.sourceKey

def correctedAppendixRows : List RetainedNameData := retainedNameRows

@[simp] theorem corrected_appendix_includes_all_four_explicit_appendix_errata :
    (correctedAppendixRows.any fun row =>
      row.retainedName = "Cymarose" ∧
        row.systematicEquivalent = "2,6-Dideoxy-3-O-methyl-ribo-hexose") = true ∧
    (correctedAppendixRows.any fun row =>
      row.retainedName = "Umbelliferose" ∧
        row.systematicEquivalent =
          "β-D-Fructofuranosyl α-D-galactopyranosyl-(1→2)-α-D-glucopyranoside") = true ∧
    (correctedAppendixRows.any fun row =>
      row.retainedName = "Acosamine" ∧
        row.systematicEquivalent = "3-Amino-2,3,6-trideoxy-L-arabino-hexose") = true ∧
    (correctedAppendixRows.any fun row =>
      row.retainedName = "Kansosamine" ∧
        row.systematicEquivalent =
          "4-Amino-4,6-dideoxy-3-C-methyl-2-O-methyl-L-mannose") = true := by
  set_option maxRecDepth 4096 in
    decide

end Carbohydrate1996AppendixErrataGlossary
end TetraStereo.OneCenter
