import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationPair01
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationPair23
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationPairs0123Separation

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem broadSurface_declarationGroup0123_distinct :
    hasDuplicateStrings
      ((broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1) ++
        (broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3)) = false := by
  rw [hasDuplicateStrings_append]
  rw [broadSurface_declarationPair01_distinct, broadSurface_declarationPairs0123_separate,
    broadSurface_declarationPair23_distinct]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
