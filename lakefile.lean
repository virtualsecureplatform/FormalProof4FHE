import Lake

open Lake DSL

package FormalProof4FHE where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`warningAsError, true⟩
  ]

require VCVio from "vendor/VCVio"
require Arklib from "vendor/ArkLib"

@[default_target]
lean_lib FormalProof4FHE

lean_lib FormalProof4FHETest
