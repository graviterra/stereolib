import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# Frozen artifact slice for 2-Carb-24--35

This lightweight module isolates the next 150 source-only carbohydrate artifacts directly from
the canonical 430-row frozen image catalog. Keeping the catalog computation outside the accumulated
source-meaning overlay prevents the kernel from unfolding the entire earlier overlay chain when
checking the exact official-page distribution.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateLateImageArtifactSlice

/-- Absolute frozen-catalog indices 228--377, from `241A.GIF` through `353C.GIF`. -/
def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  (Carbohydrate1996ImageAudit.ImageArtifact.all.drop 228).take 150

@[simp] theorem artifact_count : artifacts.length = 150 := by simp [artifacts]

def page24Artifacts := artifacts.take 19
def afterPage24Artifacts := artifacts.drop 19
def page25n26Artifacts := afterPage24Artifacts.take 16
def afterPage25n26Artifacts := afterPage24Artifacts.drop 16
def page27n28Artifacts := afterPage25n26Artifacts.take 10
def afterPage27n28Artifacts := afterPage25n26Artifacts.drop 10
def page29n30Artifacts := afterPage27n28Artifacts.take 11
def afterPage29n30Artifacts := afterPage27n28Artifacts.drop 11
def page31Artifacts := afterPage29n30Artifacts.take 20
def afterPage31Artifacts := afterPage29n30Artifacts.drop 20
def page32Artifacts := afterPage31Artifacts.take 16
def afterPage32Artifacts := afterPage31Artifacts.drop 16
def page33Artifacts := afterPage32Artifacts.take 34
def afterPage33Artifacts := afterPage32Artifacts.drop 34
def page34Artifacts := afterPage33Artifacts.take 9
def page35Artifacts := afterPage33Artifacts.drop 9

private theorem page24_source_pages :
    page24Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 19 ["24.html"] := by decide

private theorem page25n26_source_pages :
    page25n26Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 16 ["25n26.html"] := by decide

private theorem page27n28_source_pages :
    page27n28Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 10 ["27n28.html"] := by decide

private theorem page29n30_source_pages :
    page29n30Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 11 ["29n30.html"] := by decide

private theorem page31_source_pages :
    page31Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 20 ["31.html"] := by decide

private theorem page32_source_pages :
    page32Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 16 ["32.html"] := by decide

private theorem page33_source_pages :
    page33Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 34 ["33.html"] := by decide

private theorem page34_source_pages :
    page34Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 9 ["34.html"] := by decide

private theorem page35_source_pages :
    page35Artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 15 ["35.html"] := by decide

@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 19 ["24.html"] ++ List.replicate 16 ["25n26.html"] ++
        List.replicate 10 ["27n28.html"] ++ List.replicate 11 ["29n30.html"] ++
          List.replicate 20 ["31.html"] ++ List.replicate 16 ["32.html"] ++
            List.replicate 34 ["33.html"] ++ List.replicate 9 ["34.html"] ++
              List.replicate 15 ["35.html"] := by
  rw [show artifacts = page24Artifacts ++ afterPage24Artifacts by
    simp [page24Artifacts, afterPage24Artifacts]]
  rw [show afterPage24Artifacts = page25n26Artifacts ++ afterPage25n26Artifacts by
    simp [page25n26Artifacts, afterPage25n26Artifacts]]
  rw [show afterPage25n26Artifacts = page27n28Artifacts ++ afterPage27n28Artifacts by
    simp [page27n28Artifacts, afterPage27n28Artifacts]]
  rw [show afterPage27n28Artifacts = page29n30Artifacts ++ afterPage29n30Artifacts by
    simp [page29n30Artifacts, afterPage29n30Artifacts]]
  rw [show afterPage29n30Artifacts = page31Artifacts ++ afterPage31Artifacts by
    simp [page31Artifacts, afterPage31Artifacts]]
  rw [show afterPage31Artifacts = page32Artifacts ++ afterPage32Artifacts by
    simp [page32Artifacts, afterPage32Artifacts]]
  rw [show afterPage32Artifacts = page33Artifacts ++ afterPage33Artifacts by
    simp [page33Artifacts, afterPage33Artifacts]]
  rw [show afterPage33Artifacts = page34Artifacts ++ page35Artifacts by
    simp [page34Artifacts, page35Artifacts]]
  simp only [List.map_append]
  rw [page24_source_pages, page25n26_source_pages, page27n28_source_pages,
    page29n30_source_pages, page31_source_pages, page32_source_pages,
    page33_source_pages, page34_source_pages, page35_source_pages]
  simp only [List.append_assoc]

end GlobalNonDescriptorCarbohydrateLateImageArtifactSlice
end IUPACNormativeProvision
end TetraStereo.OneCenter
