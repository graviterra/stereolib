import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk7

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk7 : List (String × List String) :=
  [ ("2carb/2C3gif/337D.GIF", ["33.html"])
  , ("2carb/2C3gif/337E.GIF", ["33.html"])
  , ("2carb/2C3gif/337F.GIF", ["33.html"])
  , ("2carb/2C3gif/337G.GIF", ["33.html"])
  , ("2carb/2C3gif/341A.GIF", ["34.html"])
  , ("2carb/2C3gif/341B.GIF", ["34.html"])
  , ("2carb/2C3gif/341C.GIF", ["34.html"])
  , ("2carb/2C3gif/341D.GIF", ["34.html"])
  , ("2carb/2C3gif/341E.GIF", ["34.html"])
  , ("2carb/2C3gif/342A.GIF", ["34.html"])
  , ("2carb/2C3gif/342B.GIF", ["34.html"])
  , ("2carb/2C3gif/342C.GIF", ["34.html"])
  , ("2carb/2C3gif/342D.GIF", ["34.html"])
  , ("2carb/2C3gif/351A.GIF", ["35.html"])
  , ("2carb/2C3gif/351B.GIF", ["35.html"])
  , ("2carb/2C3gif/351C.GIF", ["35.html"])
  , ("2carb/2C3gif/351D.GIF", ["35.html"])
  , ("2carb/2C3gif/351E.GIF", ["35.html"])
  , ("2carb/2C3gif/351F.GIF", ["35.html"])
  , ("2carb/2C3gif/351G.GIF", ["35.html"])
  , ("2carb/2C3gif/351H.GIF", ["35.html"])
  , ("2carb/2C3gif/352A.GIF", ["35.html"])
  , ("2carb/2C3gif/352B.GIF", ["35.html"])
  , ("2carb/2C3gif/352C.GIF", ["35.html"])
  , ("2carb/2C3gif/352D.GIF", ["35.html"])
  , ("2carb/2C3gif/353A.GIF", ["35.html"])
  , ("2carb/2C3gif/353B.GIF", ["35.html"])
  , ("2carb/2C3gif/353C.GIF", ["35.html"])
  , ("2carb/2C3gif/362A.GIF", ["36.html"])
  , ("2carb/2C3gif/362B.GIF", ["36.html"])
  , ("2carb/2C3gif/362C.GIF", ["36.html"])
  , ("2carb/2C3gif/363A.GIF", ["36.html"])
  , ("2carb/2C3gif/363B.GIF", ["36.html"])
  , ("2carb/2C3gif/363C.GIF", ["36.html"])
  , ("2carb/2C3gif/364A.GIF", ["36.html"])
  , ("2carb/2C3gif/364B.GIF", ["36.html"])
  , ("2carb/2C3gif/371A.GIF", ["37.html"])
  , ("2carb/2C3gif/371B.GIF", ["37.html"])
  , ("2carb/2C3gif/372A.GIF", ["37.html"])
  , ("2carb/2C3gif/372B.GIF", ["37.html"])
  , ("2carb/2C3gif/372C.GIF", ["37.html"])
  , ("2carb/2C3gif/372D.GIF", ["37.html"])
  , ("2carb/2C3gif/373A.GIF", ["37.html"])
  , ("2carb/2C3gif/373B.GIF", ["37.html"])
  , ("2carb/2C3gif/373C.GIF", ["37.html"])
  , ("2carb/2C3gif/3741A.GIF", ["37.html"])
  , ("2carb/2C3gif/3741B.GIF", ["37.html"])
  , ("2carb/2C3gif/3741C.GIF", ["37.html"])
  , ("2carb/2C3gif/3742A.GIF", ["37.html"])
  , ("2carb/2C3gif/3742B.GIF", ["37.html"])
  ]

@[simp] theorem htmlImageReferrersChunk7_length : htmlImageReferrersChunk7.length = 50 := by rfl

theorem htmlImageReferrersChunk7_pathsMatchArtifacts :
    htmlImageReferrersChunk7.map Prod.fst =
      imageArtifactsChunk7.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk7_allReferenced :
    htmlImageReferrersChunk7.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk7_multiplicityCounts :
    (htmlImageReferrersChunk7.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk7.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk7.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk7.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk7.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
