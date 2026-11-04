module

public import FormalProof4FHE.HasteBoots.ObservationReplay

@[expose] public section

/-!
# Online mixed-oracle programs and counterfactual prefix replay

Every next request is specified before its result is supplied. Continuations
may depend on that result, but receive no world argument. Prefix execution
returns the actual residual program, not an abort. Its analysis budget is
not a native retry cap. Unbounded samplers still need a compatible family
of compiled prefixes and a completion/trace bridge.
-/

namespace FormalProof4FHE.HasteBoots.OracleProgram

open InputIndexedOracle (Byte Input World)
open NativeTranscript (Execution)
open ObservationReplay (Replayable)

inductive Program (A : Type) where
  | pure (value : A)
  | start (input : Input) (next : Program A)
  | read (input : Input) (offset count : ℕ) (next : Input → Program A)
  | hash (input : Input) (next : (Fin 64 → Byte) → Program A)

def bind {A B : Type} : Program A → (A → Program B) → Program B
  | .pure value, next => next value
  | .start input tail, next => .start input (bind tail next)
  | .read input offset count tail, next => .read input offset count (fun value => bind (tail value) next)
  | .hash input tail, next => .hash input (fun value => bind (tail value) next)

def run {A : Type} : Program A → World → Execution A
  | .pure value, _ => pure value
  | .start input next, world => ObservationReplay.start input >>= fun _ => run next world
  | .read input offset count next, world =>
      ObservationReplay.read world input offset count >>= fun value => run (next value) world
  | .hash input next, world => ObservationReplay.hash world input >>= fun value => run (next value) world

theorem run_bind {A B : Type} (program : Program A) (next : A → Program B) (world : World) :
    run (bind program next) world = run program world >>= fun value => run (next value) world := by
  induction program with
  | pure value => simp [bind, run]
  | start input tail ih => simp only [bind, run, ih, bind_assoc]
  | read input offset count tail ih => simp only [bind, run, ih, bind_assoc]
  | hash input tail ih => simp only [bind, run, ih, bind_assoc]

theorem run_replay {A : Type} (program : Program A) : Replayable (run program) := by
  induction program with
  | pure value => exact ObservationReplay.pure_replay value
  | start input next ih =>
      exact ObservationReplay.bind_replay (ObservationReplay.start_replay input) (fun _ => ih)
  | read input offset count next ih =>
      exact ObservationReplay.bind_replay (ObservationReplay.read_replay input offset count) ih
  | hash input next ih =>
      exact ObservationReplay.bind_replay (ObservationReplay.hash_replay input) ih

def runPrefix {A : Type} : ℕ → Program A → World → Execution (Program A ⊕ A)
  | 0, .pure value, _ => pure (.inr value)
  | 0, program, _ => pure (.inl program)
  | _ + 1, .pure value, _ => pure (.inr value)
  | fuel + 1, .start input next, world =>
      ObservationReplay.start input >>= fun _ => runPrefix fuel next world
  | fuel + 1, .read input offset count next, world =>
      ObservationReplay.read world input offset count >>= fun value => runPrefix fuel (next value) world
  | fuel + 1, .hash input next, world =>
      ObservationReplay.hash world input >>= fun value => runPrefix fuel (next value) world

/-- Agreement with only this prefix's returned bytes preserves the prefix
log and its residual program, including the next request and continuation tree. -/
theorem prefix_replay {A : Type} (fuel : ℕ) (program : Program A) :
    Replayable (runPrefix fuel program) := by
  induction fuel generalizing program with
  | zero => cases program <;> exact ObservationReplay.pure_replay _
  | succ fuel ih =>
    cases program with
    | pure value => exact ObservationReplay.pure_replay _
    | start input next =>
        exact ObservationReplay.bind_replay (ObservationReplay.start_replay input) (fun _ => ih next)
    | read input offset count next =>
        exact ObservationReplay.bind_replay (ObservationReplay.read_replay input offset count) (fun value => ih (next value))
    | hash input next =>
        exact ObservationReplay.bind_replay (ObservationReplay.hash_replay input) (fun value => ih (next value))

inductive Request where
  | start (input : Input)
  | read (input : Input) (offset count : ℕ)
  | hash (input : Input)
  deriving DecidableEq

def nextRequest {A : Type} : Program A ⊕ A → Option Request
  | .inr _ => none
  | .inl (.pure _) => none
  | .inl (.start input _) => some (.start input)
  | .inl (.read input offset count _) => some (.read input offset count)
  | .inl (.hash input _) => some (.hash input)

/-- In particular the next primitive, input, offset, and read length are
fixed by the observed past, without inspecting that primitive's response. -/
theorem next_request_replay {A : Type} (fuel : ℕ) (program : Program A) (world other : World)
    (agree : ObservationReplay.Agrees other (runPrefix fuel program world).run.2) :
    nextRequest (runPrefix fuel program other).run.1 = nextRequest (runPrefix fuel program world).run.1 :=
  congrArg (fun result => nextRequest result.1) ((prefix_replay fuel program).replay world other agree)

theorem prefix_update_unobserved {A : Type} (fuel : ℕ) (program : Program A) (world : World)
    (coordinate : InputIndexedOracle.Coordinate) (value : Byte)
    (unobserved : coordinate ∉ ObservationReplay.footprint (runPrefix fuel program world).run.2) :
    (runPrefix fuel program (Function.update world coordinate value)).run =
      (runPrefix fuel program world).run :=
  ObservationReplay.update_unobserved (prefix_replay fuel program) world coordinate value unobserved

end FormalProof4FHE.HasteBoots.OracleProgram
