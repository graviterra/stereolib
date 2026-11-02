import Lake
open Lake DSL

package «TetraStereo» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib TetraStereo where

lean_exe tetrastereo_cert where
  root := `TetraStereo.CLI.CertificateExporter
