module

public import FormalProof4FHE.HasteBoots.NativeCheckpointProgram

@[expose] public section

/-! Native prefixes which consult only SHA-512, before subsequent SHAKE
challenges. Their compiled computation is independent of the reader backend.
This is structural independence, not a probability-law or input-freshness claim. -/
namespace FormalProof4FHE.HasteBoots.NativeHashPrefix

open InputIndexedOracle (World Input)
open OracleProgram (Program bind run)

/-- No start/read action can occur, on any adaptive hash-answer branch. -/
def HashOnly {A : Type} : Program A → Prop
  | .pure _ => True
  | .hash _ next => ∀ answer, HashOnly (next answer)
  | .start _ _ => False
  | .read _ _ _ _ => False

theorem bind_hashOnly {A B : Type} (first : Program A) (next : A → Program B)
    (hashes : HashOnly first) (following : ∀ value, HashOnly (next value)) : HashOnly (bind first next) := by
  induction first with
  | pure value => exact following value
  | start input tail ih => exact hashes.elim
  | read input offset count tail ih => exact hashes.elim
  | hash input tail ih => exact fun answer => ih answer (hashes answer)

/-- Changing the entire reader function leaves this prefix's actual compiled
program unchanged, including its returned native observations. -/
theorem compile_independent {Cfg A : Type} (program : Program A) (hashes : HashOnly program)
    (left right : NativeCheckpointProgram.Reader) :
    NativeCheckpointProgram.compile (Cfg := Cfg) left program = NativeCheckpointProgram.compile right program := by
  induction program with
  | pure value => rfl
  | start input tail ih => exact hashes.elim
  | read input offset count tail ih => exact hashes.elim
  | hash input tail ih =>
    unfold NativeCheckpointProgram.compile
    congr 1
    funext answer
    rw [ih answer (hashes answer)]

/-- The retained native log of a hash-only prefix contains no reader event. -/
theorem observations_hashes {A : Type} (program : Program A) (hashes : HashOnly program) (world : World) :
    ∀ entry ∈ (run program world).run.2, ∃ input digest, entry = NativeTranscript.Observation.hash input digest := by
  induction program with
  | pure value => intro entry member; cases member
  | start input tail ih => exact hashes.elim
  | read input offset count tail ih => exact hashes.elim
  | hash input tail ih =>
    intro entry member
    change entry ∈ NativeTranscript.Observation.hash input (List.ofFn (InputIndexedOracle.sha512 world input)) ::
      (run (tail (InputIndexedOracle.sha512 world input)) world).run.2 at member
    obtain same | later := List.mem_cons.mp member
    · exact ⟨input,List.ofFn (InputIndexedOracle.sha512 world input),same⟩
    · exact ih _ (hashes _) entry later

end FormalProof4FHE.HasteBoots.NativeHashPrefix
