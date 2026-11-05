module

public import FormalProof4FHE.HasteBoots.NativeShakeReadLaw
public import FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw

@[expose] public section

/-! The checked native atomic-index program executed by the lazy compiler,
with its complete conditional distribution under mixed-oracle prequeries.
This is a real native phase, not a freshness assumption or surrogate sampler.
General mixed-program composition and scheduler integration remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeLazyIndexExecution

open InputIndexedOracle (Byte Input World law)
open NativeTranscript (Observation Transcript)
open NativeRootMessage (Digest)
open NativeShakeCache (Cache)
open NativeUsizeMessage (Usize)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp

noncomputable section

/-- Literal native response processing, with the entire original observation list. -/
def finish (transcript : Transcript) (label : Input) (domain count : Usize) (bytes : Input) :
    Option NativeIndexRequest.Result × List Observation :=
  let pending := NativeTranscript.absorb (NativeIndexRequest.prepare transcript domain) 2 label
    (TranscriptFrame.littleEndian 8 (count.val*8))
  let draws := NativeIndexRequest.ordered domain.val count.val bytes
  (some ⟨draws,NativeIndexRequest.distinct draws,NativeTranscript.absorb pending 3 label bytes⟩,
    [.start pending.input,.output pending.input 0 bytes])

def decorate (transcript : Transcript) (label : Input) (domain count : Usize) (result : Input × Cache) :
    (Option NativeIndexRequest.Result × List Observation) × Cache :=
  (finish transcript label domain count result.1,result.2)

/-- The finite-vector response law and literal native byte processing coincide. -/
theorem finish_ofFn (transcript : Transcript) (label : Input) (domain count : Usize)
    (raw : Fin (count.val*8) → Byte) :
    finish transcript label domain count (List.ofFn raw) =
      NativePrequeryIndexLaw.outcome transcript label domain count raw := rfl

/-- The actual lazy native phase is exactly the private read followed by
native framing and decoding. No hash or checkpoint effect is hidden. -/
theorem compile_request {Cfg Payload : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (cache : Cache) (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      ((NativeLazyProgram.compile (Cfg := Cfg)
        (NativeIndexRequest.request transcript label domain count)).run cache)).run state =
      (fun result => (decorate transcript label domain count result,state)) <$>
        NativeShakeReadLaw.sample (NativePrequeryIndexLaw.requestInput transcript label domain count)
          0 (count.val*8) cache := by
  simp only [NativeIndexRequest.request,valid,↓reduceIte,NativeTranscriptProgram.challengeBytes,
    NativeTranscriptProgram.query,OracleProgram.bind,NativeLazyProgram.compile,StateT.run_map,
    simulateQ_map,NativeShakeReadLaw.shared_read,map_pure,bind_pure_comp,Functor.map_map]
  rfl

/-- Invalid native dimensions reject before drawing bytes and retain both
interpreter states, including all work and exposures from the prior history. -/
theorem invalid_request {Cfg Payload : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (cache : Cache) (transcript : Transcript) (label : Input) (domain count : Usize)
    (invalid : NativeIndexRequest.check domain count ≠ true) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      ((NativeLazyProgram.compile (Cfg := Cfg)
        (NativeIndexRequest.request transcript label domain count)).run cache)).run state =
      pure (((none,[]),cache),state) := by
  simp only [NativeIndexRequest.request,ite_eq_right invalid,NativeLazyProgram.compile,
    StateT.run_pure,simulateQ_pure]

/-- The full native result/log and both interpreter states have the exact
conditional law after the whole mixed past. Partial and cloned prequeries
are retained; no premise says this index phase is fresh. -/
theorem request_event {A Cfg Payload : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (transcript : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true)
    (event : ((Option NativeIndexRequest.Result × List Observation) × Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (((OracleProgram.run (NativeIndexRequest.request transcript label domain count) other).run,
        NativeShakeHistory.writeBytes (NativeShakeKernel.observed (past world).run.2 world)
          (NativePrequeryIndexLaw.requestInput transcript label domain count) 0
          (InputIndexedOracle.bytes other (NativePrequeryIndexLaw.requestInput transcript label domain count)
            0 (count.val*8))),state)} =
      Pr{let result ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        ((NativeLazyProgram.compile (Cfg := Cfg)
          (NativeIndexRequest.request transcript label domain count)).run
          (NativeShakeKernel.observed (past world).run.2 world))).run state}[event result] := by
  rw [compile_request enc dummy shape state _ transcript label domain count valid,prEvent_map]
  have result := NativeShakeReadLaw.read_event replay world
    (NativePrequeryIndexLaw.requestInput transcript label domain count) 0 (count.val*8)
    (fun result => event (decorate transcript label domain count result,state))
  simpa only [NativePrequeryIndexLaw.request_run _ transcript label domain count valid,
    NativeShakeReadLaw.outcome,decorate,finish_ofFn,InputIndexedOracle.bytes] using result

end
end FormalProof4FHE.HasteBoots.NativeLazyIndexExecution
