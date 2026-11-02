import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateFinalImageArtifactSlice

def molecularArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  (Carbohydrate1996ImageAudit.ImageArtifact.all.drop 378).take 41

def glyphArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  (Carbohydrate1996ImageAudit.ImageArtifact.all.drop 425).take 5

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := molecularArtifacts ++ glyphArtifacts

@[simp] theorem molecular_artifact_count : molecularArtifacts.length = 41 := by
  simp [molecularArtifacts]

@[simp] theorem glyph_artifact_count : glyphArtifacts.length = 5 := by
  simp [glyphArtifacts]

@[simp] theorem artifact_count : artifacts.length = 46 := by
  simp [artifacts]

def page36Artifacts := molecularArtifacts.take 8
def afterPage36Artifacts := molecularArtifacts.drop 8
def page37Artifacts := afterPage36Artifacts.take 16
def afterPage37Artifacts := afterPage36Artifacts.drop 16
def page38Artifacts := afterPage37Artifacts.take 5
def page39Artifacts := afterPage37Artifacts.drop 5

private theorem page36_source_pages :
    page36Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 8 ["36.html"] := by decide

private theorem page37_source_pages :
    page37Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 16 ["37.html"] := by decide

private theorem page38_source_pages :
    page38Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 5 ["38.html"] := by decide

private theorem page39_source_pages :
    page39Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 12 ["39.html"] := by decide

@[simp] theorem molecular_source_pages_exact :
    molecularArtifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 8 ["36.html"] ++ List.replicate 16 ["37.html"] ++
        List.replicate 5 ["38.html"] ++ List.replicate 12 ["39.html"] := by
  rw [show molecularArtifacts = page36Artifacts ++ afterPage36Artifacts by
    simp [page36Artifacts, afterPage36Artifacts]]
  rw [show afterPage36Artifacts = page37Artifacts ++ afterPage37Artifacts by
    simp [page37Artifacts, afterPage37Artifacts]]
  rw [show afterPage37Artifacts = page38Artifacts ++ page39Artifacts by
    simp [page38Artifacts, page39Artifacts]]
  simp only [List.map_append]
  rw [page36_source_pages, page37_source_pages, page38_source_pages, page39_source_pages]
  simp only [List.append_assoc]

@[simp] theorem glyph_source_pages_exact :
    glyphArtifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      [ ["00n01.html", "03n04.html", "05.html", "06n07.html", "11n12.html", "16.html",
          "17.html", "18.html", "22.html", "23.html", "24.html", "31.html", "33.html",
          "37.html", "app.html", "index.html", "ref.html"]
      , ["36.html", "37.html"]
      , ["06n07.html", "36.html", "37.html", "39.html", "er372.html", "errat.html"]
      , ["errat.html"]
      , ["06n07.html"] ] := by
  decide

end GlobalNonDescriptorCarbohydrateFinalImageArtifactSlice
end IUPACNormativeProvision
end TetraStereo.OneCenter
