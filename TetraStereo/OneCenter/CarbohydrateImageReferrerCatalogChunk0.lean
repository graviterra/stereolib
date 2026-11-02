import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk0

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk0 : List (String × List String) :=
  [ ("2carb/2C0gif/022.GIF", ["02.html"])
  , ("2carb/2C0gif/0222A.GIF", ["02.html"])
  , ("2carb/2C0gif/0222B.GIF", ["02.html"])
  , ("2carb/2C0gif/02231.GIF", ["02.html"])
  , ("2carb/2C0gif/02232.GIF", ["02.html"])
  , ("2carb/2C0gif/02233.GIF", ["02.html"])
  , ("2carb/2C0gif/03A.GIF", ["03n04.html"])
  , ("2carb/2C0gif/03B.GIF", ["03n04.html"])
  , ("2carb/2C0gif/041A.GIF", ["03n04.html"])
  , ("2carb/2C0gif/041B.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042A.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042B.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042C.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042D.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042E.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042F.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042G.GIF", ["03n04.html"])
  , ("2carb/2C0gif/042H.GIF", ["03n04.html"])
  , ("2carb/2C0gif/052A.GIF", ["05.html"])
  , ("2carb/2C0gif/052B.GIF", ["05.html"])
  , ("2carb/2C0gif/052C.GIF", ["05.html"])
  , ("2carb/2C0gif/052D.GIF", ["05.html"])
  , ("2carb/2C0gif/052E.GIF", ["05.html"])
  , ("2carb/2C0gif/053A.GIF", ["05.html"])
  , ("2carb/2C0gif/053B.GIF", ["05.html"])
  , ("2carb/2C0gif/053C.GIF", ["05.html"])
  , ("2carb/2C0gif/053D.GIF", ["05.html"])
  , ("2carb/2C0gif/054A.GIF", ["05.html"])
  , ("2carb/2C0gif/054B.GIF", ["05.html"])
  , ("2carb/2C0gif/054C.GIF", ["05.html"])
  , ("2carb/2C0gif/054D.GIF", ["05.html"])
  , ("2carb/2C0gif/054E.GIF", ["05.html"])
  , ("2carb/2C0gif/054F.GIF", ["05.html"])
  , ("2carb/2C0gif/054G.GIF", ["05.html"])
  , ("2carb/2C0gif/054H.GIF", ["05.html"])
  , ("2carb/2C0gif/054I.GIF", ["05.html"])
  , ("2carb/2C0gif/055.GIF", ["05.html"])
  , ("2carb/2C0gif/056A.GIF", ["05.html"])
  , ("2carb/2C0gif/056B.GIF", ["05.html"])
  , ("2carb/2C0gif/057.GIF", ["05.html"])
  , ("2carb/2C0gif/058A.GIF", ["05.html"])
  , ("2carb/2C0gif/058B.GIF", ["05.html"])
  , ("2carb/2C0gif/062A.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062B.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062C.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062D.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062E.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062F.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062G.GIF", ["06n07.html"])
  , ("2carb/2C0gif/062H.GIF", ["06n07.html"])
  ]

@[simp] theorem htmlImageReferrersChunk0_length : htmlImageReferrersChunk0.length = 50 := by rfl

theorem htmlImageReferrersChunk0_pathsMatchArtifacts :
    htmlImageReferrersChunk0.map Prod.fst =
      imageArtifactsChunk0.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk0_allReferenced :
    htmlImageReferrersChunk0.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk0_multiplicityCounts :
    (htmlImageReferrersChunk0.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk0.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk0.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk0.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk0.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
