module
public import FormalProof4FHE.HasteBoots.OracleMachine
@[expose] public section

/-! A finite causal oracle prelude and an unbounded machine form one causal
machine. No cache or history is reset at the boundary. This is a chronological
oracle-trace bridge; local computation and physical costs remain separate. -/
namespace FormalProof4FHE.HasteBoots.OracleMachinePrelude
open OracleProgram (Program run)
open OracleMachine (Command take)
open InputIndexedOracle (World Input)
noncomputable section

def lift {S A : Type} : Command S A → Command (Program S) A
  | .done value => .done value
  | .start input next => .start input (.pure next)
  | .read input offset count next => .read input offset count (fun value => .pure (next value))
  | .hash input next => .hash input (fun value => .pure (next value))

def prepend {S A : Type} (step : S → Command S A) : Program S → Command (Program S) A
  | .pure state => lift (step state)
  | .start input next => .start input next
  | .read input offset count next => .read input offset count next
  | .hash input next => .hash input next

theorem post_log {S A : Type} (step : S → Command S A) (fuel : ℕ) (state : S) (world : World) :
    (run (take (prepend step) fuel (.pure state)) world).run.2 = (run (take step fuel state) world).run.2 := by
  induction fuel generalizing state with
  | zero => cases selected : step state <;> simp only [take,prepend,selected,lift] <;> rfl
  | succ fuel ih =>
    cases selected : step state with
    | done value => simp only [take,prepend,selected,lift]; rfl
    | start input next =>
      simp only [take,prepend,selected,lift]
      change .start input :: (run (take (prepend step) fuel (.pure next)) world).run.2 = _
      rw [ih]
      rfl
    | read input offset count next =>
      simp only [take,prepend,selected,lift]
      change .output input offset (InputIndexedOracle.bytes world input offset count) ::
        (run (take (prepend step) fuel (.pure (next (InputIndexedOracle.bytes world input offset count)))) world).run.2 = _
      rw [ih]
      rfl
    | hash input next =>
      simp only [take,prepend,selected,lift]
      change .hash input (List.ofFn (InputIndexedOracle.sha512 world input)) ::
        (run (take (prepend step) fuel (.pure (next (InputIndexedOracle.sha512 world input)))) world).run.2 = _
      rw [ih]
      rfl

theorem prelude_log {S A : Type} (step : S → Command S A) (prelude : Program S) (fuel : ℕ) (world : World) :
    (run (take (prepend step) ((run prelude world).run.2.length+fuel) prelude) world).run.2 =
      (run prelude world).run.2 ++ (run (take step fuel (run prelude world).run.1) world).run.2 := by
  induction prelude with
  | pure state =>
    change (run (take (prepend step) (0+fuel) (.pure state)) world).run.2 =
      [] ++ (run (take step fuel state) world).run.2
    simpa only [Nat.zero_add,List.nil_append] using post_log step fuel state world
  | start input next ih =>
    change (run (take (prepend step) (((run next world).run.2.length+1)+fuel) (.start input next)) world).run.2 = _
    rw [Nat.add_right_comm _ 1 fuel]
    change .start input :: (run (take (prepend step) ((run next world).run.2.length+fuel) next) world).run.2 = _
    rw [ih]
    rfl
  | read input offset count next ih =>
    change (run (take (prepend step) (((run (next (InputIndexedOracle.bytes world input offset count)) world).run.2.length+1)+fuel)
      (.read input offset count next)) world).run.2 = _
    rw [Nat.add_right_comm _ 1 fuel]
    change .output input offset (InputIndexedOracle.bytes world input offset count) ::
      (run (take (prepend step) ((run (next (InputIndexedOracle.bytes world input offset count)) world).run.2.length+fuel)
        (next (InputIndexedOracle.bytes world input offset count))) world).run.2 = _
    rw [ih]
    rfl
  | hash input next ih =>
    change (run (take (prepend step) (((run (next (InputIndexedOracle.sha512 world input)) world).run.2.length+1)+fuel)
      (.hash input next)) world).run.2 = _
    rw [Nat.add_right_comm _ 1 fuel]
    change .hash input (List.ofFn (InputIndexedOracle.sha512 world input)) ::
      (run (take (prepend step) ((run (next (InputIndexedOracle.sha512 world input)) world).run.2.length+fuel)
        (next (InputIndexedOracle.sha512 world input))) world).run.2 = _
    rw [ih]
    rfl
end
end FormalProof4FHE.HasteBoots.OracleMachinePrelude
