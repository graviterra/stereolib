import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk6

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk6 : List (String × List String) :=
  [ ("2carb/2C3gif/312Q.GIF", ["31.html"])
  , ("2carb/2C3gif/313A.GIF", ["31.html"])
  , ("2carb/2C3gif/313B.GIF", ["31.html"])
  , ("2carb/2C3gif/313C.GIF", ["31.html"])
  , ("2carb/2C3gif/321A.GIF", ["32.html"])
  , ("2carb/2C3gif/321B.GIF", ["32.html"])
  , ("2carb/2C3gif/321C.GIF", ["32.html"])
  , ("2carb/2C3gif/321D.GIF", ["32.html"])
  , ("2carb/2C3gif/322A.GIF", ["32.html"])
  , ("2carb/2C3gif/322B.GIF", ["32.html"])
  , ("2carb/2C3gif/322C.GIF", ["32.html"])
  , ("2carb/2C3gif/322D.GIF", ["32.html"])
  , ("2carb/2C3gif/322E.GIF", ["32.html"])
  , ("2carb/2C3gif/322F.GIF", ["32.html"])
  , ("2carb/2C3gif/323A.GIF", ["32.html"])
  , ("2carb/2C3gif/323B.GIF", ["32.html"])
  , ("2carb/2C3gif/323C.GIF", ["32.html"])
  , ("2carb/2C3gif/323D.GIF", ["32.html"])
  , ("2carb/2C3gif/324A.GIF", ["32.html"])
  , ("2carb/2C3gif/324B.GIF", ["32.html"])
  , ("2carb/2C3gif/331.GIF", ["33.html"])
  , ("2carb/2C3gif/332A.GIF", ["33.html"])
  , ("2carb/2C3gif/332B.GIF", ["33.html"])
  , ("2carb/2C3gif/332C.GIF", ["33.html"])
  , ("2carb/2C3gif/332D.GIF", ["33.html"])
  , ("2carb/2C3gif/332E.GIF", ["33.html"])
  , ("2carb/2C3gif/332F.GIF", ["33.html"])
  , ("2carb/2C3gif/332G.GIF", ["33.html"])
  , ("2carb/2C3gif/332H.GIF", ["33.html"])
  , ("2carb/2C3gif/332I.GIF", ["33.html"])
  , ("2carb/2C3gif/333A.GIF", ["33.html"])
  , ("2carb/2C3gif/333B.GIF", ["33.html"])
  , ("2carb/2C3gif/333C.GIF", ["33.html"])
  , ("2carb/2C3gif/333D.GIF", ["33.html"])
  , ("2carb/2C3gif/334A.GIF", ["33.html"])
  , ("2carb/2C3gif/334B.GIF", ["33.html"])
  , ("2carb/2C3gif/335A.GIF", ["33.html"])
  , ("2carb/2C3gif/335B.GIF", ["33.html"])
  , ("2carb/2C3gif/335C.GIF", ["33.html"])
  , ("2carb/2C3gif/335D.GIF", ["33.html"])
  , ("2carb/2C3gif/335E.GIF", ["33.html"])
  , ("2carb/2C3gif/336A.GIF", ["33.html"])
  , ("2carb/2C3gif/336B.GIF", ["33.html"])
  , ("2carb/2C3gif/336C.GIF", ["33.html"])
  , ("2carb/2C3gif/336D.GIF", ["33.html"])
  , ("2carb/2C3gif/336E.GIF", ["33.html"])
  , ("2carb/2C3gif/336F.GIF", ["33.html"])
  , ("2carb/2C3gif/337A.GIF", ["33.html"])
  , ("2carb/2C3gif/337B.GIF", ["33.html"])
  , ("2carb/2C3gif/337C.GIF", ["33.html"])
  ]

@[simp] theorem htmlImageReferrersChunk6_length : htmlImageReferrersChunk6.length = 50 := by rfl

theorem htmlImageReferrersChunk6_pathsMatchArtifacts :
    htmlImageReferrersChunk6.map Prod.fst =
      imageArtifactsChunk6.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk6_allReferenced :
    htmlImageReferrersChunk6.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk6_multiplicityCounts :
    (htmlImageReferrersChunk6.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk6.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk6.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk6.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk6.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
