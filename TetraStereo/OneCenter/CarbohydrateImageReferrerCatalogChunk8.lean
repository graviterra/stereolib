import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk8

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk8 : List (String × List String) :=
  [ ("2carb/2C3gif/375A.GIF", ["37.html"])
  , ("2carb/2C3gif/375B.GIF", ["37.html"])
  , ("2carb/2C3gif/383A.GIF", ["38.html"])
  , ("2carb/2C3gif/383B.GIF", ["38.html"])
  , ("2carb/2C3gif/385A.GIF", ["38.html"])
  , ("2carb/2C3gif/385B.GIF", ["38.html"])
  , ("2carb/2C3gif/385C.GIF", ["38.html"])
  , ("2carb/2C3gif/392.GIF", ["39.html"])
  , ("2carb/2C3gif/393A.GIF", ["39.html"])
  , ("2carb/2C3gif/393B.GIF", ["39.html"])
  , ("2carb/2C3gif/394.GIF", ["39.html"])
  , ("2carb/2C3gif/395.GIF", ["39.html"])
  , ("2carb/2C3gif/397A.GIF", ["39.html"])
  , ("2carb/2C3gif/397B.GIF", ["39.html"])
  , ("2carb/2C3gif/397C.GIF", ["39.html"])
  , ("2carb/2C3gif/398A.GIF", ["39.html"])
  , ("2carb/2C3gif/398B.GIF", ["39.html"])
  , ("2carb/2C3gif/399A.GIF", ["39.html"])
  , ("2carb/2C3gif/399B.GIF", ["39.html"])
  , ("2carb/2C3gif/GLOSA.GIF", ["glo.html"])
  , ("2carb/2C3gif/GLOSB.GIF", ["glo.html"])
  , ("2carb/2C3gif/GLOSC.GIF", ["glo.html"])
  , ("2carb/2C3gif/GLOSD.GIF", ["glo.html"])
  , ("2carb/2C3gif/GLOSE.GIF", ["glo.html"])
  , ("2carb/2C3gif/LYGL1.GIF", ["33.html", "er336.html", "errat.html"])
  , ("greek/ALTER.GIF", ["00n01.html", "03n04.html", "05.html", "06n07.html", "11n12.html", "16.html", "17.html", "18.html", "22.html", "23.html", "24.html", "31.html", "33.html", "37.html", "app.html", "index.html", "ref.html"])
  , ("greek/ARROWB.GIF", ["36.html", "37.html"])
  , ("greek/ARROWR.GIF", ["06n07.html", "36.html", "37.html", "39.html", "er372.html", "errat.html"])
  , ("greek/BETA.GIF", ["errat.html"])
  , ("greek/RETARR.GIF", ["06n07.html"])
  ]

@[simp] theorem htmlImageReferrersChunk8_length : htmlImageReferrersChunk8.length = 30 := by rfl

theorem htmlImageReferrersChunk8_pathsMatchArtifacts :
    htmlImageReferrersChunk8.map Prod.fst =
      imageArtifactsChunk8.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk8_allReferenced :
    htmlImageReferrersChunk8.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk8_multiplicityCounts :
    (htmlImageReferrersChunk8.filter fun entry => entry.2.length = 1).length = 26 ∧
    (htmlImageReferrersChunk8.filter fun entry => entry.2.length = 2).length = 1 ∧
    (htmlImageReferrersChunk8.filter fun entry => entry.2.length = 3).length = 1 ∧
    (htmlImageReferrersChunk8.filter fun entry => entry.2.length = 6).length = 1 ∧
    (htmlImageReferrersChunk8.filter fun entry => entry.2.length = 17).length = 1 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
