import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk3

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk3 : List (String × List String) :=
  [ ("2carb/2C1gif/173C.GIF", ["17.html"])
  , ("2carb/2C1gif/173D.GIF", ["17.html"])
  , ("2carb/2C1gif/173E.GIF", ["17.html"])
  , ("2carb/2C1gif/181A.GIF", ["18.html"])
  , ("2carb/2C1gif/181B.GIF", ["18.html"])
  , ("2carb/2C1gif/181C.GIF", ["18.html"])
  , ("2carb/2C1gif/181D.GIF", ["18.html"])
  , ("2carb/2C1gif/181E.GIF", ["18.html"])
  , ("2carb/2C1gif/181F.GIF", ["18.html"])
  , ("2carb/2C1gif/181G.GIF", ["18.html"])
  , ("2carb/2C1gif/181H.GIF", ["18.html"])
  , ("2carb/2C1gif/183A.GIF", ["18.html"])
  , ("2carb/2C1gif/183B.GIF", ["18.html"])
  , ("2carb/2C1gif/183C.GIF", ["18.html"])
  , ("2carb/2C1gif/183D.GIF", ["18.html"])
  , ("2carb/2C1gif/183E.GIF", ["18.html"])
  , ("2carb/2C1gif/183F.GIF", ["18.html"])
  , ("2carb/2C1gif/183G.GIF", ["18.html"])
  , ("2carb/2C1gif/184.GIF", ["18.html"])
  , ("2carb/2C1gif/191A.GIF", ["19.html"])
  , ("2carb/2C1gif/191B.GIF", ["19.html"])
  , ("2carb/2C1gif/191C.GIF", ["19.html"])
  , ("2carb/2C1gif/191D.GIF", ["19.html"])
  , ("2carb/2C1gif/191E.GIF", ["19.html"])
  , ("2carb/2C1gif/191F.GIF", ["19.html"])
  , ("2carb/2C1gif/192A.GIF", ["19.html"])
  , ("2carb/2C1gif/192B.GIF", ["19.html"])
  , ("2carb/2C2gif/201A.GIF", ["20.html"])
  , ("2carb/2C2gif/201B.GIF", ["20.html"])
  , ("2carb/2C2gif/201C.GIF", ["20.html"])
  , ("2carb/2C2gif/202A.GIF", ["20.html"])
  , ("2carb/2C2gif/202B.GIF", ["20.html"])
  , ("2carb/2C2gif/202C.GIF", ["20.html"])
  , ("2carb/2C2gif/202D.GIF", ["20.html"])
  , ("2carb/2C2gif/202E.GIF", ["20.html"])
  , ("2carb/2C2gif/202F.GIF", ["20.html"])
  , ("2carb/2C2gif/202G.GIF", ["20.html"])
  , ("2carb/2C2gif/202H.GIF", ["20.html"])
  , ("2carb/2C2gif/202I.GIF", ["20.html"])
  , ("2carb/2C2gif/202J.GIF", ["20.html"])
  , ("2carb/2C2gif/211A.GIF", ["21.html"])
  , ("2carb/2C2gif/211B.GIF", ["21.html"])
  , ("2carb/2C2gif/211C.GIF", ["21.html"])
  , ("2carb/2C2gif/211D.GIF", ["21.html"])
  , ("2carb/2C2gif/212A.GIF", ["21.html"])
  , ("2carb/2C2gif/212B.GIF", ["21.html"])
  , ("2carb/2C2gif/212C.GIF", ["21.html"])
  , ("2carb/2C2gif/212D.GIF", ["21.html"])
  , ("2carb/2C2gif/222A.GIF", ["22.html"])
  , ("2carb/2C2gif/222B.GIF", ["22.html"])
  ]

@[simp] theorem htmlImageReferrersChunk3_length : htmlImageReferrersChunk3.length = 50 := by rfl

theorem htmlImageReferrersChunk3_pathsMatchArtifacts :
    htmlImageReferrersChunk3.map Prod.fst =
      imageArtifactsChunk3.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk3_allReferenced :
    htmlImageReferrersChunk3.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk3_multiplicityCounts :
    (htmlImageReferrersChunk3.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk3.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk3.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk3.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk3.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
