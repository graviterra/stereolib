import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk0
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk1
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk2
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk3
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunk4
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks01
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks02
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks03
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks04
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks12
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks13
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks14
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks23
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks24
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationChunks34
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationGroup0123
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationGroup0123Separation

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem broadSurface_suiteDeclarationNames_distinct :
    hasDuplicateStrings broadSurfaceSuiteDeclarationNames = false := by
  rw [broadSurface_suiteDeclarationNames_chunks]
  rw [show broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1 ++
        broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3 ++
          broadSurfaceDeclarationChunk4 =
      ((broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1) ++
        (broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3)) ++
          broadSurfaceDeclarationChunk4 by
    simp only [List.append_assoc]]
  rw [hasDuplicateStrings_append]
  rw [broadSurface_declarationGroup0123_distinct,
    broadSurface_declarationGroup0123_separate, broadSurface_declarationChunk4_distinct]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
