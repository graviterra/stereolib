import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks04
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks14
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks24
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks34

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem broadSurface_declarationGroup0123_separate :
    stringListsIntersect
      ((broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1) ++
        (broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3))
      broadSurfaceDeclarationChunk4 = false := by
  rw [stringListsIntersect_append_left, stringListsIntersect_append_left,
    stringListsIntersect_append_left]
  rw [broadSurface_declarationChunks04_separate, broadSurface_declarationChunks14_separate,
    broadSurface_declarationChunks24_separate, broadSurface_declarationChunks34_separate]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
