import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk1

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Carbohydrate1996ImageAudit

def htmlImageReferrersChunk1 : List (String × List String) :=
  [ ("2carb/2C0gif/063A.GIF", ["06n07.html"])
  , ("2carb/2C0gif/063B.GIF", ["06n07.html"])
  , ("2carb/2C0gif/064A.GIF", ["06n07.html"])
  , ("2carb/2C0gif/064B.GIF", ["06n07.html"])
  , ("2carb/2C0gif/071A.GIF", ["06n07.html"])
  , ("2carb/2C0gif/071B.GIF", ["06n07.html"])
  , ("2carb/2C0gif/074.GIF", ["06n07.html"])
  , ("2carb/2C0gif/083A.GIF", ["08n09.html"])
  , ("2carb/2C0gif/083B.GIF", ["08n09.html"])
  , ("2carb/2C0gif/084.GIF", ["08n09.html"])
  , ("2carb/2C0gif/09A.GIF", ["08n09.html"])
  , ("2carb/2C0gif/09B.GIF", ["08n09.html"])
  , ("2carb/2C0gif/09C.GIF", ["08n09.html"])
  , ("2carb/2C0gif/09D.GIF", ["08n09.html"])
  , ("2carb/2C0gif/09E.GIF", ["08n09.html"])
  , ("2carb/2C1gif/102.GIF", ["10.html"])
  , ("2carb/2C1gif/104A.GIF", ["10.html"])
  , ("2carb/2C1gif/104B.GIF", ["10.html"])
  , ("2carb/2C1gif/104C.GIF", ["10.html"])
  , ("2carb/2C1gif/104D.GIF", ["10.html"])
  , ("2carb/2C1gif/104E.GIF", ["10.html"])
  , ("2carb/2C1gif/104F.GIF", ["10.html"])
  , ("2carb/2C1gif/104G.GIF", ["10.html"])
  , ("2carb/2C1gif/104H.GIF", ["10.html"])
  , ("2carb/2C1gif/104I.GIF", ["10.html"])
  , ("2carb/2C1gif/111A.GIF", ["11n12.html"])
  , ("2carb/2C1gif/111B.GIF", ["11n12.html"])
  , ("2carb/2C1gif/112A.GIF", ["11n12.html"])
  , ("2carb/2C1gif/112B.GIF", ["11n12.html"])
  , ("2carb/2C1gif/112C.GIF", ["11n12.html"])
  , ("2carb/2C1gif/112D.GIF", ["11n12.html"])
  , ("2carb/2C1gif/112E.GIF", ["11n12.html"])
  , ("2carb/2C1gif/121A.GIF", ["11n12.html"])
  , ("2carb/2C1gif/121B.GIF", ["11n12.html"])
  , ("2carb/2C1gif/121C.GIF", ["11n12.html"])
  , ("2carb/2C1gif/131A.GIF", ["13.html"])
  , ("2carb/2C1gif/131B.GIF", ["13.html"])
  , ("2carb/2C1gif/131C.GIF", ["13.html"])
  , ("2carb/2C1gif/131D.GIF", ["13.html"])
  , ("2carb/2C1gif/131E.GIF", ["13.html"])
  , ("2carb/2C1gif/131F.GIF", ["13.html"])
  , ("2carb/2C1gif/132.GIF", ["13.html"])
  , ("2carb/2C1gif/133A.GIF", ["13.html"])
  , ("2carb/2C1gif/133B.GIF", ["13.html"])
  , ("2carb/2C1gif/133C.GIF", ["13.html"])
  , ("2carb/2C1gif/133D.GIF", ["13.html"])
  , ("2carb/2C1gif/133E.GIF", ["13.html"])
  , ("2carb/2C1gif/133F.GIF", ["13.html"])
  , ("2carb/2C1gif/133G.GIF", ["13.html"])
  , ("2carb/2C1gif/133H.GIF", ["13.html"])
  ]

@[simp] theorem htmlImageReferrersChunk1_length : htmlImageReferrersChunk1.length = 50 := by rfl

theorem htmlImageReferrersChunk1_pathsMatchArtifacts :
    htmlImageReferrersChunk1.map Prod.fst =
      imageArtifactsChunk1.map ImageArtifactData.relativePath := by
  decide

theorem htmlImageReferrersChunk1_allReferenced :
    htmlImageReferrersChunk1.all (fun entry => decide (entry.2 ≠ [])) = true := by
  decide

theorem htmlImageReferrersChunk1_multiplicityCounts :
    (htmlImageReferrersChunk1.filter fun entry => entry.2.length = 1).length = 50 ∧
    (htmlImageReferrersChunk1.filter fun entry => entry.2.length = 2).length = 0 ∧
    (htmlImageReferrersChunk1.filter fun entry => entry.2.length = 3).length = 0 ∧
    (htmlImageReferrersChunk1.filter fun entry => entry.2.length = 6).length = 0 ∧
    (htmlImageReferrersChunk1.filter fun entry => entry.2.length = 17).length = 0 := by
  decide

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
