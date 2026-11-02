import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk2
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk3
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks23

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem broadSurface_declarationPair23_distinct :
    hasDuplicateStrings (broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3) = false := by
  rw [hasDuplicateStrings_append]
  rw [broadSurface_declarationChunk2_distinct, broadSurface_declarationChunks23_separate,
    broadSurface_declarationChunk3_distinct]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
