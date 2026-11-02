import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk0
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk1
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks01

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem broadSurface_declarationPair01_distinct :
    hasDuplicateStrings (broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1) = false := by
  rw [hasDuplicateStrings_append]
  rw [broadSurface_declarationChunk0_distinct, broadSurface_declarationChunks01_separate,
    broadSurface_declarationChunk1_distinct]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
