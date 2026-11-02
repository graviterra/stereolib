import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk4

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk4 : List (String × List String) :=
  [ ("2carb/2C2gif/222C.GIF", ["22.html"])
  , ("2carb/2C2gif/222D.GIF", ["22.html"])
  , ("2carb/2C2gif/222E.GIF", ["22.html"])
  , ("2carb/2C2gif/222F.GIF", ["22.html"])
  , ("2carb/2C2gif/222G.GIF", ["22.html"])
  , ("2carb/2C2gif/222H.GIF", ["22.html"])
  , ("2carb/2C2gif/222I.GIF", ["22.html"])
  , ("2carb/2C2gif/222J.GIF", ["22.html"])
  , ("2carb/2C2gif/222K.GIF", ["22.html"])
  , ("2carb/2C2gif/222L.GIF", ["22.html"])
  , ("2carb/2C2gif/222M.GIF", ["22.html"])
  , ("2carb/2C2gif/222N.GIF", ["22.html"])
  , ("2carb/2C2gif/222O.GIF", ["22.html"])
  , ("2carb/2C2gif/222P.GIF", ["22.html"])
  , ("2carb/2C2gif/231A.GIF", ["23.html"])
  , ("2carb/2C2gif/231B.GIF", ["23.html"])
  , ("2carb/2C2gif/231C.GIF", ["23.html"])
  , ("2carb/2C2gif/232A.GIF", ["23.html"])
  , ("2carb/2C2gif/232B.GIF", ["23.html"])
  , ("2carb/2C2gif/232C.GIF", ["23.html"])
  , ("2carb/2C2gif/233A.GIF", ["23.html"])
  , ("2carb/2C2gif/233B.GIF", ["23.html"])
  , ("2carb/2C2gif/233C.GIF", ["23.html"])
  , ("2carb/2C2gif/234A.GIF", ["23.html"])
  , ("2carb/2C2gif/234B.GIF", ["23.html"])
  , ("2carb/2C2gif/234C.GIF", ["23.html"])
  , ("2carb/2C2gif/234D.GIF", ["23.html"])
  , ("2carb/2C2gif/234E.GIF", ["23.html"])
  , ("2carb/2C2gif/241A.GIF", ["24.html"])
  , ("2carb/2C2gif/241B.GIF", ["24.html"])
  , ("2carb/2C2gif/241C.GIF", ["24.html"])
  , ("2carb/2C2gif/241D.GIF", ["24.html"])
  , ("2carb/2C2gif/241E.GIF", ["24.html"])
  , ("2carb/2C2gif/2421A.GIF", ["24.html"])
  , ("2carb/2C2gif/2421B.GIF", ["24.html"])
  , ("2carb/2C2gif/2421C.GIF", ["24.html"])
  , ("2carb/2C2gif/2421D.GIF", ["24.html"])
  , ("2carb/2C2gif/2421E.GIF", ["24.html"])
  , ("2carb/2C2gif/2421F.GIF", ["24.html"])
  , ("2carb/2C2gif/2421G.GIF", ["24.html"])
  , ("2carb/2C2gif/2421H.GIF", ["24.html"])
  , ("2carb/2C2gif/2421I.GIF", ["24.html"])
  , ("2carb/2C2gif/2422A.GIF", ["24.html"])
  , ("2carb/2C2gif/2422B.GIF", ["24.html"])
  , ("2carb/2C2gif/2422C.GIF", ["24.html"])
  , ("2carb/2C2gif/243A.GIF", ["24.html"])
  , ("2carb/2C2gif/243B.GIF", ["24.html"])
  , ("2carb/2C2gif/25A.GIF", ["25n26.html"])
  , ("2carb/2C2gif/25B.GIF", ["25n26.html"])
  , ("2carb/2C2gif/25C.GIF", ["25n26.html"])
  ]

@[simp] theorem htmlImageReferrersChunk4_length : htmlImageReferrersChunk4.length = 50 := by rfl

theorem htmlImageReferrersChunk4_pathsMatchArtifacts :
    htmlImageReferrersChunk4.map Prod.fst =
      imageArtifactsChunk4.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk4_allReferenced :
    htmlImageReferrersChunk4.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk4_multiplicityCounts :
    (htmlImageReferrersChunk4.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk4.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk4.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk4.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk4.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
