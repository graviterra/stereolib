import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk5

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk5 : List (String × List String) :=
  [ ("2carb/2C2gif/25D.GIF", ["25n26.html"])
  , ("2carb/2C2gif/25E.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26A.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26B.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26C.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26D.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26E.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26F.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26G.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26H.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26I.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26J.GIF", ["25n26.html"])
  , ("2carb/2C2gif/26K.GIF", ["25n26.html"])
  , ("2carb/2C2gif/27A.GIF", ["27n28.html"])
  , ("2carb/2C2gif/27B.GIF", ["27n28.html"])
  , ("2carb/2C2gif/27C.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28A.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28B.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28C.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28D.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28E.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28F.GIF", ["27n28.html"])
  , ("2carb/2C2gif/28G.GIF", ["27n28.html"])
  , ("2carb/2C2gif/29A.GIF", ["29n30.html"])
  , ("2carb/2C2gif/29B.GIF", ["29n30.html"])
  , ("2carb/2C2gif/29C.GIF", ["29n30.html"])
  , ("2carb/2C2gif/29D.GIF", ["29n30.html"])
  , ("2carb/2C2gif/29E.GIF", ["29n30.html"])
  , ("2carb/2C3gif/30A.GIF", ["29n30.html"])
  , ("2carb/2C3gif/30B.GIF", ["29n30.html"])
  , ("2carb/2C3gif/30C.GIF", ["29n30.html"])
  , ("2carb/2C3gif/30D.GIF", ["29n30.html"])
  , ("2carb/2C3gif/30E.GIF", ["29n30.html"])
  , ("2carb/2C3gif/30F.GIF", ["29n30.html"])
  , ("2carb/2C3gif/312A.GIF", ["31.html"])
  , ("2carb/2C3gif/312B.GIF", ["31.html"])
  , ("2carb/2C3gif/312C.GIF", ["31.html"])
  , ("2carb/2C3gif/312D.GIF", ["31.html"])
  , ("2carb/2C3gif/312E.GIF", ["31.html"])
  , ("2carb/2C3gif/312F.GIF", ["31.html"])
  , ("2carb/2C3gif/312G.GIF", ["31.html"])
  , ("2carb/2C3gif/312H.GIF", ["31.html"])
  , ("2carb/2C3gif/312I.GIF", ["31.html"])
  , ("2carb/2C3gif/312J.GIF", ["31.html"])
  , ("2carb/2C3gif/312K.GIF", ["31.html"])
  , ("2carb/2C3gif/312L.GIF", ["31.html"])
  , ("2carb/2C3gif/312M.GIF", ["31.html"])
  , ("2carb/2C3gif/312N.GIF", ["31.html"])
  , ("2carb/2C3gif/312O.GIF", ["31.html"])
  , ("2carb/2C3gif/312P.GIF", ["31.html"])
  ]

@[simp] theorem htmlImageReferrersChunk5_length : htmlImageReferrersChunk5.length = 50 := by rfl

theorem htmlImageReferrersChunk5_pathsMatchArtifacts :
    htmlImageReferrersChunk5.map Prod.fst =
      imageArtifactsChunk5.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk5_allReferenced :
    htmlImageReferrersChunk5.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk5_multiplicityCounts :
    (htmlImageReferrersChunk5.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk5.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk5.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk5.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk5.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
