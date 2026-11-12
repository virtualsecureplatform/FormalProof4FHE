module
public import FormalProof4FHE.HasteBoots.CheckpointRecordScope
public import FormalProof4FHE.HasteBoots.NativeCheckpointProgram
@[expose] public section

/-! Native compiled callbacks cannot issue ghost checkpoint annotations.
This structural fact needs no honesty or SHAKE freshness assumption. -/
namespace FormalProof4FHE.HasteBoots.CompiledCheckpointScope
open OracleSpec OracleComp CheckpointRecordScope
noncomputable section
variable {Cfg A : Type}

/-- The existing native compiler emits only hashes and pure observations;
all start/read/hash branches are covered for every reader backend. -/
theorem compile (scope : Cfg → Prop) (reader : NativeCheckpointProgram.Reader)
    (program : OracleProgram.Program A) :
    Scoped scope (NativeCheckpointProgram.compile (Cfg := Cfg) reader program) := by
  induction program with
  | pure value => exact pure_scoped scope _
  | start input next ih => exact map_scoped scope _ ih _
  | read input offset count next ih => exact map_scoped scope _ (ih _) _
  | hash input next ih =>
    apply bind_scoped scope _ _ (query_scoped scope (.inr (.inl input)) trivial)
    intro answer
    exact map_scoped scope _ (ih answer) _

end
end FormalProof4FHE.HasteBoots.CompiledCheckpointScope
