module
import all FormalProof4FHE.HasteBoots.CausalSeedExposure
import all FormalProof4FHE.HasteBoots.NativeDirectRootFreeze
import all Mathlib.Data.List.Sort
import all Init.Data.String.Defs
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
namespace HasteBootsCausalRootFreezeSmoke

def profile : NativeRootMessage.Digest := fun _ => 0
def seed : NativeRootMessage.Digest := fun _ => 41
def otherSeed : NativeRootMessage.Digest := fun _ => 99
def sources : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[(profile,seed),(profile,seed),(seed,seed)],by decide⟩
def rootInput : Input := TranscriptFrame.encodeMany
  [⟨1,NativeCanonicalLookupWire.registryLabel,NativeCanonicalLookupWire.sourcesCodec.encode sources⟩]

def past : List NativeTranscript.Observation := [.output rootInput 3 [0]]
example : (NativeDirectRootFreeze.fresh [] rootInput).length = 2 := by decide +kernel
example : NativeDirectRootFreeze.fresh past rootInput = [] := by decide +kernel
example : (NativeDirectRootFreeze.fresh [.start rootInput,.output rootInput 0 []] rootInput).length = 2 := by decide +kernel
example : (NativeDirectRootFreeze.fresh [.hash rootInput (List.replicate 64 0)] rootInput).length = 2 := by decide +kernel
example : NativeDirectRootFreeze.inputRoots [255] = [] := by decide +kernel
example : (NativeDirectRootFreeze.seen (past++[.output [255] 0 [0]])).card = 2 := by decide +kernel

def childKey : Input := TranscriptFrame.encodeMany (NativeChildSeedView.seededFrames profile [7] [9] seed)
def parentKey : Input := [7,9]
def step (state : ℕ) : OracleMachine.Command ℕ Unit :=
  if state = 0 then .read childKey 0 1 (fun _ => 1) else
  if state = 1 then .read parentKey 63 1 (fun _ => 2) else .done ()
def world : World := fun _ => 0

example : CausalSeedExposure.firstRead step (OracleProgram.run (OracleMachine.take step 1 0) world).run = some parentKey := by
  decide +kernel
example : CausalSeedExposure.firstRead step (OracleProgram.run (OracleMachine.take step 2 0) world).run = none := by
  decide +kernel
example : CausalSeedExposure.firstRead step (.inl 1,[.output parentKey 63 [0]]) = none := by decide +kernel
example : CausalSeedExposure.firstRead (fun _ : Unit => (OracleMachine.Command.read parentKey 64 1 (fun _ => ())) : Unit → OracleMachine.Command Unit Unit)
    (.inl (),[]) = none := by decide +kernel
example : CausalSeedExposure.firstRead (fun _ : Unit => (OracleMachine.Command.read parentKey 0 0 (fun _ => ())) : Unit → OracleMachine.Command Unit Unit)
    (.inl (),[]) = none := by decide +kernel

noncomputable section
example : CausalSeedExposure.risk step (OracleProgram.run (OracleMachine.take step 1 0) world).run =
    1/(2 : ENNReal)^512 := by
  have selected : CausalSeedExposure.firstRead step (OracleProgram.run (OracleMachine.take step 1 0) world).run = some parentKey := by
    decide +kernel
  have count : (NativeChildSeedView.guesses (OracleProgram.run (OracleMachine.take step 1 0) world).run.2).card = 1 := by
    decide +kernel
  simp only [CausalSeedExposure.risk,selected,count,Nat.cast_one]

example : (InputIndexedOracle.law[|{other | (OracleProgram.run (OracleMachine.take step 1 0) other).run =
    (OracleProgram.run (OracleMachine.take step 1 0) world).run}]) {other |
      CausalSeedExposure.event step (OracleProgram.run (OracleMachine.take step 1 0) other).run other} =
    1/(2 : ENNReal)^512 := by
  rw [CausalSeedExposure.conditional_event step (OracleProgram.run_replay _) world]
  have selected : CausalSeedExposure.firstRead step (OracleProgram.run (OracleMachine.take step 1 0) world).run = some parentKey := by
    decide +kernel
  have count : (NativeChildSeedView.guesses (OracleProgram.run (OracleMachine.take step 1 0) world).run.2).card = 1 := by
    decide +kernel
  simp only [CausalSeedExposure.risk,selected,count,Nat.cast_one]

/-- Removing the annotations preserves the exact original oracle computation and owned cache. -/
example (cache : NativeShakeCache.Cache) :
    simulateQ NativeDirectRootFreeze.erase
      ((NativeDirectRootFreeze.compile [] (.read rootInput 0 1 (fun _ => .pure ()))).run cache) =
      (NativeLazyProgram.compile (Cfg := NativeRootMessage.Digest) (.read rootInput 0 1 (fun _ => .pure ()))).run cache :=
  NativeDirectRootFreeze.erase_compile [] _ cache


def shape (_ : NativeRootMessage.Digest) : BinaryTree.Skeleton := .leaf
def cached : NativeShakeCache.Cache := fun _ => some 0

def once : OracleProgram.Program Unit := .read rootInput 0 1 (fun _ => .pure ())
def twice : OracleProgram.Program Unit := .read rootInput 0 1 (fun _ => .read rootInput 1 1 (fun _ => .pure ()))

private theorem sample_cached (offset : ℕ) : NativeShakeReadLaw.sample rootInput offset 1 cached = pure ([0],cached) := by
  simp [NativeShakeReadLaw.sample,NativeShakeKernel.step,NativeShakeKernel.answer,NativeShakeKernel.install,cached]

example : (fun result => result.2.checkpoints.checkpoints.length) <$>
    NativeDirectRootFreeze.execute NativeGoldColumnAuthentication.encoding profile shape [] once cached
      (CheckpointExecution.empty shape) = pure 2 := by
  rw [once,NativeDirectRootFreeze.execute_read _ _ _ _ _ _ _ _ _ _ (by decide),sample_cached,pure_bind,
    NativeDirectRootFreeze.execute_pure,pure_bind,map_pure]
  congr 1
  decide +kernel

example : (fun result => result.2.checkpoints.checkpoints.length) <$>
    NativeDirectRootFreeze.execute NativeGoldColumnAuthentication.encoding profile shape [] twice cached
      (CheckpointExecution.empty shape) = pure 2 := by
  rw [twice,NativeDirectRootFreeze.execute_read _ _ _ _ _ _ _ _ _ _ (by decide),sample_cached,pure_bind,
    NativeDirectRootFreeze.execute_read _ _ _ _ _ _ _ _ _ _ (by decide),sample_cached,pure_bind,
    NativeDirectRootFreeze.execute_pure,pure_bind,pure_bind,map_pure]
  rw [NativeDirectRootFreeze.fresh_after_output [] rootInput 0 [0] (by decide)]
  congr 1
  decide +kernel

example : (fun result => result.2.checkpoints.checkpoints.length) <$>
    NativeDirectRootFreeze.execute NativeGoldColumnAuthentication.encoding profile shape []
      (.read rootInput 0 0 (fun _ => .pure ())) cached (CheckpointExecution.empty shape) = pure 0 := by
  rw [NativeDirectRootFreeze.execute_zero,NativeDirectRootFreeze.execute_pure,map_pure,map_pure]
  rfl


/-- The actual parsed context/root key is retained at the actual pre-read hash log. -/
example (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape)
    (result : ((Unit × List NativeTranscript.Observation) × NativeShakeCache.Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := NativeRootMessage.Digest) shape)
    (possible : result ∈ support (NativeDirectRootFreeze.execute NativeGoldColumnAuthentication.encoding profile shape []
      once cache state)) :
    ⟨profile,⟨seed,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  NativeDirectRootFreeze.read_snapshot NativeGoldColumnAuthentication.encoding profile shape [] rootInput 0 1
    (fun _ => .pure ()) cache state (by decide) (profile,seed) (by decide +kernel) result possible

example : NativeDirectRootFreeze.compile [] twice = (do
    let first ← NativeDirectRootFreeze.compile [] (NativeProgramPrefix.take 1 twice)
    let second ← NativeDirectRootFreeze.compile first.2 (NativeProgramPrefix.resume first.1)
    pure (second.1,first.2++second.2)) := by
  simpa only [List.nil_append] using NativeDirectRootFreeze.compile_resume [] 1 twice

end
end HasteBootsCausalRootFreezeSmoke

/-- info: 'FormalProof4FHE.HasteBoots.CausalSeedExposure.firstRead_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalSeedExposure.firstRead_fresh

/-- info: 'FormalProof4FHE.HasteBoots.CausalSeedExposure.conditional_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalSeedExposure.conditional_event

/-- info: 'FormalProof4FHE.HasteBoots.CausalSeedExposure.event_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalSeedExposure.event_measurable

/-- info: 'FormalProof4FHE.HasteBoots.CausalSeedExposure.averaged_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CausalSeedExposure.averaged_event

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_byte

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_roots

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.erase_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.canonical_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.canonical_erase

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.canonical_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.canonical_compile

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_erasure

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_pure

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_zero

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.execute_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.fresh_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.fresh_mem

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.seen_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.seen_append

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.seen_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.seen_output

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.fresh_after_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.fresh_after_output

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.compile_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.compile_bind

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.compile_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.compile_resume

/-- info: 'FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.read_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeDirectRootFreeze.read_snapshot
