import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks02
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks03
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks12
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks13

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem broadSurface_declarationPairs0123_separate :
    stringListsIntersect
      (broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1)
      (broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3) = false := by
  rw [stringListsIntersect_append_left]
  rw [stringListsIntersect_append_right, stringListsIntersect_append_right]
  rw [broadSurface_declarationChunks02_separate, broadSurface_declarationChunks03_separate,
    broadSurface_declarationChunks12_separate, broadSurface_declarationChunks13_separate]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
