module
import all FormalProof4FHE.HasteBoots.NativeGoldHelperVerification
import all FormalProof4FHETest.HasteBootsPcsClaimSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World Byte)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
open OracleSpec OracleComp
namespace HasteBootsCausalPcsSmoke
noncomputable section

def world : World
  | .inl (_,offset) => ⟨offset % 256,Nat.mod_lt _ (by decide)⟩
  | .inr (input,_) => input.head?.getD 0

def worker (tag : Byte) : OracleComp (Input →ₒ Digest) Bool :=
  .queryBind [tag] (fun first => .queryBind [42] (fun common => pure (first 0 == tag && common 0 == 42)))
def workers : HashWorkerPool.Workers Input Digest 2 := fun index => worker (if index.val = 0 then 1 else 2)
def choose (_ : HashWorkerPool.Workers Input Digest 2) (memory : ℕ) : Program (Option (Fin 2) × ℕ) :=
  .start [99] (.read [99] memory 1 (fun _ => .hash [42] (fun _ => .pure (some ⟨memory%2,Nat.mod_lt _ (by decide)⟩,memory+1))))
def pool (fuel : ℕ) := (run (CausalHashWorkerPool.program choose fuel workers 0) world).run
example : HashWorkerPool.allAccepted (pool 4).1.workers = true := by decide +kernel
example : (pool 4).1.memory = 4 ∧ (pool 4).2.length = 16 := by decide +kernel
example : (JointHashCache.project (pool 4).2).keys.card = 3 := by decide +kernel
example : ((pool 4).2.filterMap (fun event => match event with | .hash input _ => some input | _ => none)).count [42] = 6 := by decide +kernel
example (index : Fin 2) : simulateQ (JointHashCache.project (pool 4).2).cache.toPartialImpl (workers index) = some true := by
  simpa only [pool,List.nil_append,List.append_nil] using CausalHashWorkerPool.accepted_actual choose 4 workers 0 world [] []
    (by intro entry member; cases member) (by intro entry member; cases member) (by decide +kernel) index
example (first extra : ℕ) : (pool first).2.IsPrefix (pool (first+extra)).2 := CausalHashWorkerPool.log_prefix choose first extra workers 0 world

def cancel (workers : HashWorkerPool.Workers Input Digest 2) (memory : ℕ) : Program (Option (Fin 2) × ℕ) :=
  if memory = 1 then .pure (none,memory+1) else choose workers memory
def cancelled := (run (CausalHashWorkerPool.program cancel 20 workers 0) world).run
example : cancelled.1.memory = 2 ∧ cancelled.2.length = 4 := by decide +kernel
example : HashWorkerPool.allAccepted cancelled.1.workers = false := by decide +kernel
example : (run (CausalHashWorkerPool.tick (pure true : OracleComp (Input →ₒ Digest) Bool)) world).run.2 = [] := rfl
example : (run (CausalHashWorkerPool.program choose 20 (fun _ => pure true) 0) world).run.2 = [] := rfl

open NativePcsClaimSmoke (blockTables retainedParameters parent)
def select (cancel : Bool) (work : NativeGoldPcsWorkers.Prepared)
    (_ : HashWorkerPool.Workers Input Digest work.jobs.length) (_ : Unit) : Program (Option (Fin work.jobs.length) × Unit) :=
  .pure (if cancel then none else if positive : 0 < work.jobs.length then some ⟨0,positive⟩ else none,())
def tag : NativeGoldPcsProgram.Outcome Unit → ℕ
  | .prefix _ => 0
  | .completed _ completion => match completion.status with
    | .accepted _ => 1
    | .columns => 2
    | .claim .claim => 3
    | .suspended => 4
    | .claim .finish => 5

def canonical (fuel : ℕ) (cancel : Bool) := match NativePcsClaimSmoke.Canonical.query,NativePcsClaimSmoke.Canonical.opening with
  | some query,some proof => (run (NativeGoldPcsProgram.program
      ⟨blockTables,retainedParameters,parent,NativePcsClaimSmoke.Canonical.root,query,NativePcsClaimSmoke.Canonical.claimed,proof,18⟩
      (select cancel) fuel ()) NativePcsClaimSmoke.Canonical.world).run
  | _,_ => (NativeGoldPcsProgram.Outcome.prefix .pairingUnavailable,[])
example : tag (canonical 6 false).1 = 1 := by decide +kernel
example : (canonical 6 false).2 = NativePcsClaimSmoke.Canonical.expected := by decide +kernel
example : tag (canonical 5 false).1 = 4 := by decide +kernel
example : tag (canonical 6 true).1 = 4 := by decide +kernel
example : (canonical 6 true).2 = NativePcsClaimSmoke.Canonical.expected.take 24 := by decide +kernel

def badClaim (fuel : ℕ) := match NativePcsClaimSmoke.ZeroBad.query,NativePcsClaimSmoke.ZeroBad.opening with
  | some query,some proof => (run (NativeGoldPcsProgram.program
      ⟨blockTables,retainedParameters,parent,NativePcsClaimSmoke.ZeroBad.root,query,NativePcsClaimSmoke.ZeroBad.claimed,proof,18⟩
      (select false) fuel ()) NativePcsClaimSmoke.ZeroBad.world).run
  | _,_ => (NativeGoldPcsProgram.Outcome.prefix .pairingUnavailable,[])
example : tag (badClaim 6).1 = 3 := by decide +kernel
example : (badClaim 6).2 = NativePcsClaimSmoke.ZeroBad.expected := by decide +kernel

open NativeGoldHelperVerification (Progress Result)
def calls : List (NativeSharedLookupHelpers.Call NativeGoldPcsOpening.Opening) :=
  match NativePcsClaimSmoke.Canonical.query,NativePcsClaimSmoke.Canonical.opening with
  | some query,some proof => [⟨NativePcsClaimSmoke.Canonical.root,query,NativePcsClaimSmoke.Canonical.claimed,proof⟩]
  | _,_ => []
def helpers (fuel : ℕ) (cancel : Bool) := (run (NativeGoldHelperVerification.loop blockTables retainedParameters 18
  (select cancel) fuel calls ⟨parent,(),[]⟩) NativePcsClaimSmoke.Canonical.world).run
def resultTag : Result Unit → ℕ
  | .done _ => 1
  | .stopped _ _ outcome => tag outcome + 10
example : resultTag (helpers 6 false).1 = 1 ∧ (helpers 6 false).1.progress.receipts.length = 1 := by decide +kernel
example : (helpers 6 false).2 = NativePcsClaimSmoke.Canonical.expected := by decide +kernel
example : resultTag (helpers 5 false).1 = 14 ∧ (helpers 5 false).1.progress.receipts.length = 0 := by decide +kernel
example : resultTag (helpers 6 true).1 = 14 ∧ (helpers 6 true).2 = NativePcsClaimSmoke.Canonical.expected.take 24 := by decide +kernel
-- Cancellation at the first call retains its observations and never starts the remaining calls.
def repeatedCancelled := (run (NativeGoldHelperVerification.loop blockTables retainedParameters 18
  (select true) 6 (calls ++ calls) ⟨parent,(),[]⟩) NativePcsClaimSmoke.Canonical.world).run
example : resultTag repeatedCancelled.1 = 14 ∧ repeatedCancelled.2 = (helpers 6 true).2 := by decide +kernel
example : (helpers 6 false).1.progress.receipts.map (fun receipt => receipt.call.values.val.map Fin.val) =
    calls.map (fun call => call.values.val.map Fin.val) := by decide +kernel
-- Reusing this fixture at the changed parent stops the second call while retaining the first receipt.
def repeated := (run (NativeGoldHelperVerification.loop blockTables retainedParameters 18
  (select false) 6 (calls ++ calls) ⟨parent,(),[]⟩) NativePcsClaimSmoke.Canonical.world).run
example : (match repeated.1 with | .stopped _ _ _ => true | _ => false) = true ∧
    repeated.1.progress.receipts.length = 1 := by decide +kernel

-- The real outer protocol must finish its preflight before a helper scheduler can run.
def emptyProof : NativeSharedLookupProofData.Proof NativeGoldPcsOpening.Opening Unit :=
  ⟨⟨⟨[],by decide⟩,by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩,(),⟨[],by decide⟩⟩
def emptyContext : NativeGoldHelperVerification.Context Unit :=
  ⟨blockTables,⟨[],by decide⟩,retainedParameters,parent,⟨[],by decide⟩,emptyProof,18,18,18,18,6⟩
def probe : NativeGoldPcsProgram.Scheduler Unit := fun _ _ _ =>
  .hash [255] (fun _ => .pure (none,()))
def emptyRun := (run (NativeGoldHelperVerification.program emptyContext probe ()) world).run
example : (match emptyRun.1 with | .prior (none,none) => true | _ => false) = true := by decide +kernel
example : emptyRun.2 = [] := by decide +kernel


def badCalls : List (NativeSharedLookupHelpers.Call NativeGoldPcsOpening.Opening) :=
  match NativePcsClaimSmoke.ZeroBad.query,NativePcsClaimSmoke.ZeroBad.opening with
  | some query,some proof => [⟨NativePcsClaimSmoke.ZeroBad.root,query,NativePcsClaimSmoke.ZeroBad.claimed,proof⟩]
  | _,_ => []
def rejectedHelpers := (run (NativeGoldHelperVerification.loop blockTables retainedParameters 18
  (select false) 6 (badCalls ++ calls) ⟨parent,(),[]⟩) NativePcsClaimSmoke.ZeroBad.world).run
example : resultTag rejectedHelpers.1 = 13 ∧ rejectedHelpers.1.progress.receipts.length = 0 := by decide +kernel
example : rejectedHelpers.2 = NativePcsClaimSmoke.ZeroBad.expected := by decide +kernel

end
end HasteBootsCausalPcsSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CausalHashWorkerPool.known_sublist' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalHashWorkerPool.known_sublist

/-- info: 'FormalProof4FHE.HasteBoots.CausalHashWorkerPool.tick_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalHashWorkerPool.tick_replay

/-- info: 'FormalProof4FHE.HasteBoots.CausalHashWorkerPool.program_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalHashWorkerPool.program_replays

/-- info: 'FormalProof4FHE.HasteBoots.CausalHashWorkerPool.accepted_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalHashWorkerPool.accepted_replays

/-- info: 'FormalProof4FHE.HasteBoots.CausalHashWorkerPool.accepted_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalHashWorkerPool.accepted_actual

/-- info: 'FormalProof4FHE.HasteBoots.CausalHashWorkerPool.log_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalHashWorkerPool.log_prefix

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.completed_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.completed_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.accepted_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.accepted_flags

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.accepted_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.accepted_value

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.accepted_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsProgram.accepted_workers

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.advance_spec' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.advance_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.loop_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.loop_trace

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.Trace.order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.Trace.order

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.Trace.receipts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.Trace.receipts

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_order

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_receipts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_receipts

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldHelperVerification.helpers_workers
