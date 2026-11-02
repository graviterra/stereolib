import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk2

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk2 : List (String × List String) :=
  [ ("2carb/2C1gif/134A.GIF", ["13.html"])
  , ("2carb/2C1gif/134B.GIF", ["13.html"])
  , ("2carb/2C1gif/142A.GIF", ["14n15.html"])
  , ("2carb/2C1gif/142B.GIF", ["14n15.html"])
  , ("2carb/2C1gif/142C.GIF", ["14n15.html"])
  , ("2carb/2C1gif/143A.GIF", ["14n15.html"])
  , ("2carb/2C1gif/143B.GIF", ["14n15.html"])
  , ("2carb/2C1gif/143C.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15A.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15B.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15C.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15D.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15E.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15F.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15G.GIF", ["14n15.html"])
  , ("2carb/2C1gif/15H.GIF", ["14n15.html"])
  , ("2carb/2C1gif/161A.GIF", ["16.html"])
  , ("2carb/2C1gif/161B.GIF", ["16.html"])
  , ("2carb/2C1gif/161C.GIF", ["16.html"])
  , ("2carb/2C1gif/162A.GIF", ["16.html"])
  , ("2carb/2C1gif/162B.GIF", ["16.html"])
  , ("2carb/2C1gif/163.GIF", ["16.html"])
  , ("2carb/2C1gif/164A.GIF", ["16.html"])
  , ("2carb/2C1gif/164B.GIF", ["16.html"])
  , ("2carb/2C1gif/164C.GIF", ["16.html"])
  , ("2carb/2C1gif/165A.GIF", ["16.html"])
  , ("2carb/2C1gif/165B.GIF", ["16.html"])
  , ("2carb/2C1gif/165C.GIF", ["16.html"])
  , ("2carb/2C1gif/165D.GIF", ["16.html"])
  , ("2carb/2C1gif/166A.GIF", ["16.html"])
  , ("2carb/2C1gif/166B.GIF", ["16.html"])
  , ("2carb/2C1gif/172A.GIF", ["17.html"])
  , ("2carb/2C1gif/172B.GIF", ["17.html"])
  , ("2carb/2C1gif/172C.GIF", ["17.html"])
  , ("2carb/2C1gif/172D.GIF", ["17.html"])
  , ("2carb/2C1gif/172E.GIF", ["17.html"])
  , ("2carb/2C1gif/172F.GIF", ["17.html"])
  , ("2carb/2C1gif/172G.GIF", ["17.html"])
  , ("2carb/2C1gif/172H.GIF", ["17.html"])
  , ("2carb/2C1gif/172I.GIF", ["17.html"])
  , ("2carb/2C1gif/172J.GIF", ["17.html"])
  , ("2carb/2C1gif/172K.GIF", ["17.html"])
  , ("2carb/2C1gif/172L.GIF", ["17.html"])
  , ("2carb/2C1gif/172M.GIF", ["17.html"])
  , ("2carb/2C1gif/172N.GIF", ["17.html"])
  , ("2carb/2C1gif/172O.GIF", ["17.html"])
  , ("2carb/2C1gif/172P.GIF", ["17.html"])
  , ("2carb/2C1gif/172Q.GIF", ["17.html"])
  , ("2carb/2C1gif/173A.GIF", ["17.html"])
  , ("2carb/2C1gif/173B.GIF", ["17.html"])
  ]

@[simp] theorem htmlImageReferrersChunk2_length : htmlImageReferrersChunk2.length = 50 := by rfl

theorem htmlImageReferrersChunk2_pathsMatchArtifacts :
    htmlImageReferrersChunk2.map Prod.fst =
      imageArtifactsChunk2.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk2_allReferenced :
    htmlImageReferrersChunk2.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk2_multiplicityCounts :
    (htmlImageReferrersChunk2.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk2.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk2.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk2.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk2.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
