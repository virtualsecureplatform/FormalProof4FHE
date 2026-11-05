module

import all FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices
import all Mathlib.Data.List.Sort
import all Init.Data.String.Defs

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)

namespace HasteBootsPrequeryIndexSmoke

def input : Input := [7,9]
def actual : World
  | .inl (_,position) => if position = 0 then 7 else if position = 8 then 5 else 0
  | .inr _ => 0

def prequery : OracleProgram.Program Input := .read input 0 1 .pure

def cached (raw : Fin 16 → Byte) : Fin 16 → Byte :=
  CachedOracleResponse.mask
    (ObservationReplay.footprint (OracleProgram.run prequery actual).run.2)
    actual (CachedOracleResponse.shakeCoordinates input 0 16) raw

example : cached (fun _ => 0) 0 = 7 := by decide +kernel
example : cached (fun _ => 0) 8 = 0 := by decide +kernel
example : cached (fun _ => 1) 0 = 7 := by decide +kernel
example : cached (fun _ => 1) 8 = 1 := by decide +kernel

example : (List.ofFn (NativeIndexRequest.typedDraws 3 2 (cached (fun _ => 0)))).map Fin.val =
    [7,0] := by decide +kernel
example : (List.ofFn (NativeIndexRequest.typedDraws 3 2 (cached (fun _ => 1)))).map Fin.val =
    [7,1] := by decide +kernel

/-- Unseen input bytes are not populated by an equal offset in another input. -/
example : CachedOracleResponse.mask
    (ObservationReplay.footprint (OracleProgram.run prequery actual).run.2)
    actual (CachedOracleResponse.shakeCoordinates [7,9,0] 0 16) (fun _ => 1) 0 = 1 := by
  decide +kernel

/-- A cloned reader exposes the same coordinate set, rather than fresh coins. -/
example : ObservationReplay.footprint
    [.output input 0 [7],.output input 0 [7]] =
    ObservationReplay.footprint [.output input 0 [7]] := by decide +kernel

/-- A prequery to discarded high bits does not fix the low-bit draw. -/
example : (NativeIndexRequest.typedDraws 3 2
    (CachedOracleResponse.mask (ObservationReplay.footprint [.output input 7 [255]])
      (fun _ => 255) (CachedOracleResponse.shakeCoordinates input 0 16) (fun _ => 1))) 0 = 1 := by
  decide +kernel

example : (NativeGoldPcsDraws.typed 3 2
    (NativeIndexRequest.ordered 8 2 (List.ofFn (cached (fun _ => 7))))).map
      (fun draws => (List.ofFn draws).map Fin.val) = some [7,7] := by decide +kernel
example : NativeIndexRequest.distinct [7,7] = [7] := by decide +kernel

/-- Full prior exposure makes both words independent of the fresh generator. -/
example : (List.ofFn (NativeIndexRequest.typedDraws 3 2
    (CachedOracleResponse.mask (ObservationReplay.footprint
      (OracleProgram.run (.read input 0 16 (.pure : Input → OracleProgram.Program Input)) actual).run.2)
      actual (CachedOracleResponse.shakeCoordinates input 0 16) (fun _ => 255)))).map Fin.val =
    [7,5] := by decide +kernel

def transcript : NativeTranscript.Transcript := NativeTranscript.new [1] (fun _ => 0)
def domain : NativeUsizeMessage.Usize := ⟨8,by decide⟩
def quota : NativeUsizeMessage.Usize := ⟨2,by decide⟩

example : NativeIndexRequest.check domain quota = true := by decide +kernel
example : (NativePrequeryIndexLaw.outcome transcript [3] domain quota
    (cached (fun _ => 7))).1.map (fun result => result.draws) = some [7,7] := by decide +kernel
example : (NativePrequeryIndexLaw.outcome transcript [3] domain quota
    (cached (fun _ => 7))).1.map (fun result => result.indices) = some [7] := by decide +kernel
example : ((OracleProgram.run (NativeIndexRequest.request transcript [3] domain quota) actual).run.1).map
    (fun result => result.draws) = some [7,5] := by decide +kernel


def nativePast : OracleProgram.Program Input :=
  .read (NativePrequeryIndexLaw.requestInput transcript [3] domain quota) 0 16 .pure

def choose (past : Input × List NativeTranscript.Observation) : NativePrequeryIndexLaw.Request :=
  ⟨transcript,if past.1.headD 0 = 7 then [3] else [4],domain,quota⟩

/-- The request is selected after the complete framed input was prequeried. -/
example : (choose (OracleProgram.run nativePast actual).run).label = [3] := by decide +kernel

example : (NativePrequeryIndexLaw.outcome transcript
    (choose (OracleProgram.run nativePast actual).run).label domain quota
      (CachedOracleResponse.mask
        (ObservationReplay.footprint (OracleProgram.run nativePast actual).run.2) actual
        (CachedOracleResponse.shakeCoordinates
          (NativePrequeryIndexLaw.requestInput transcript [3] domain quota) 0 16) (fun _ => 255))).1.map
      (fun result => result.draws) = some [7,5] := by decide +kernel

end HasteBootsPrequeryIndexSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.conditional_draws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.conditional_draws

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.conditional_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.conditional_event

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.fresh_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.fresh_agreement

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.repeated_draws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.repeated_draws

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.ordered_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.ordered_event

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.adaptive_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.adaptive_event

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.request_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.request_run

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.request_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.request_event

/-- info: 'FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.adaptive_request_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePrequeryIndexLaw.adaptive_request_event

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices.typed_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices.typed_ofFn

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices.typed_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices.typed_ordered

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices.checked_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPrequeryIndices.checked_event
