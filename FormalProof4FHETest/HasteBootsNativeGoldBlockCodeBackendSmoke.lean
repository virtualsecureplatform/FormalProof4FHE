module
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
import all FormalProof4FHE.HasteBoots.NativeFields

import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
import all FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate

import all FormalProof4FHE.HasteBoots.ConcreteNTTRootPowerArray
import all FormalProof4FHE.HasteBoots.ConcreteNTTPlanRootPowers

import all FormalProof4FHE.HasteBoots.ConcreteNTTBitReverse
import all FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleIndices
import all FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleArray
import all FormalProof4FHE.HasteBoots.ConcreteNTTConstructedTwiddles

import all FormalProof4FHE.HasteBoots.ConcreteNTTPlanConstants
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldPlan
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldTable

import all FormalProof4FHE.HasteBoots.ConcreteNTTCacheLookup
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldCache
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldCacheRCU

import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeLayout
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldCapturedAttempt
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeProgram
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeBackend

import all FormalProof4FHE.HasteBoots.NativeGoldBlockCode
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
import all FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext
import all FormalProof4FHE.HasteBoots.NativeGoldRowEncoding
import all FormalProof4FHE.HasteBoots.NativeGoldNtt
import all FormalProof4FHE.HasteBoots.NativeGoldArithmetic
import all FormalProof4FHE.HasteBoots.NativeGoldSolinas
import all FormalProof4FHE.HasteBoots.NativeFieldRepresentation
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeFieldWire
import all FormalProof4FHE.HasteBoots.NativeBrakedownContext
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all Mathlib.Data.Nat.Size
import all Init.Data.String.Defs

namespace FormalProof4FHETest.HasteBootsNativeGoldBlockCodeBackendSmoke
open FormalProof4FHE.HasteBoots
open NativeGoldBlockCodeProgram (Request Config Phase)
private def usize (n : Nat) : NativeUsizeMessage.Usize := Fin.ofNat (2^64) n
private def request (message block blowup : Nat) : Request := ⟨usize message,usize block,usize blowup⟩
-- A finite observed prefix for tests only; the constructor has no retry fuel.
private def steps (input : Request) : Nat → Config → Config
  | 0,config => config
  | n+1,config => steps input n (NativeGoldBlockCodeProgram.tick input config)
private theorem steps_reachable (input : Request) (n : Nat) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable input config) :
    NativeGoldBlockCodeProgram.Reachable input (steps input n config) := by
  induction n generalizing config with
  | zero => exact reachable
  | succ n ih => exact ih _ (.tick reachable)

-- Exact source rejection classes, before any generation or cache initialization.
/-- info: true -/
#guard_msgs in
#eval [(0,1,2,NativeGoldBlockCode.Error.dimensions), (1,0,2,.dimensions),
       (1,1,1,.dimensions), (1,1,3,.dimensions),
       (18446744073709551615,1,2,.messageOverflow),
       (9223372036854775808,1,2,.domainOverflow),
       (1,18446744073709551615,2,.codewordOverflow)].all fun (m,b,e,error) =>
  let finalState := NativeGoldBlockCodeProgram.tick (request m b e) {}
  decide (finalState.phase = Phase.error error) && decide (finalState.cache = ({} : ConcreteNTTGoldCacheRCU.Machine))

-- First table generation rejects unsupported domains before touching caches.
/-- info: true -/
#guard_msgs in
#eval let finalState := steps (request 2147483648 1 2) 2 {}
  decide (finalState.phase = Phase.error .generation) && decide (finalState.cache = ({} : ConcreteNTTGoldCacheRCU.Machine))

-- The original generation call precedes initialization, even on a warm cache.
/-- info: true -/
#guard_msgs in
#eval let input := request 7 3 2
  let first := NativeGoldBlockCodeProgram.tick input {}
  let second := NativeGoldBlockCodeProgram.tick input first
  match first.phase,second.phase with
  | .generating _,.initializing _ => decide (first.cache = second.cache ∧ second.cache.current.tables = [])
  | _,_ => false

-- Complete code objects contain every retained dimension and exact native root.
/-- info: true -/
#guard_msgs in
#eval [(1,1,2,1,32,549755813888), (7,3,2,4,32,549755813888),
       (1024,4,4,256,1024,455906449640507599),
       (4096,4,4,1024,4096,1532612707718625687)].all fun (m,b,e,padded,count,root) =>
  let finalState := steps (request m b e) 6 {}
  match finalState.phase with
  | .done result => decide (result.code.messageLength.val = m ∧ result.code.blockWidth.val = b ∧
      result.code.messageBlocks.val = padded ∧ result.code.blocks.val = count ∧ result.code.domainRoot.val = root ∧
      result.loaded.root.val = root ∧ finalState.cache.current.tables.length = 1 ∧ finalState.rejected = [])
  | _ => false

-- A competing publication makes the held snapshot stale; its proposal is retained.
/-- info: true -/
#guard_msgs in
#eval let input := request 1024 4 4
  let pending := steps input 4 {}
  let captured := ConcreteNTTGoldCacheRCU.capture pending.cache
  match ConcreteNTTGoldCacheRCU.attempt 5 captured (ConcreteNTTGoldCacheRCU.newest pending.cache) with
  | .committed other =>
    let resumed : Config := {pending with cache := other}
    let rejected := NativeGoldBlockCodeProgram.tick input resumed
    match rejected.phase with
    | .capturing _ => decide (rejected.rejected.map (List.map Prod.fst) = [[10]] ∧ rejected.cache.current.tables.map Prod.fst = [5])
    | _ => false
  | _ => false

-- Recapturing and retrying retains the competing table and completes the code.
/-- info: true -/
#guard_msgs in
#eval let input := request 1024 4 4
  let pending := steps input 4 {}
  let captured := ConcreteNTTGoldCacheRCU.capture pending.cache
  match ConcreteNTTGoldCacheRCU.attempt 5 captured (ConcreteNTTGoldCacheRCU.newest pending.cache) with
  | .committed other =>
    let rejected := NativeGoldBlockCodeProgram.tick input {pending with cache := other}
    let finalState := steps input 3 rejected
    match finalState.phase with
    | .done result => decide (finalState.cache.current.tables.map Prod.fst = [5,10] ∧ result.code.domainRoot.val = 455906449640507599 ∧ finalState.rejected.length = 1)
    | _ => false
  | _ => false

-- Warm-cache construction still enters generation, then reuses the retained table.
/-- info: true -/
#guard_msgs in
#eval let input := request 7 3 2
  let cold := steps input 6 {}
  let warm : Config := {cache := cold.cache}
  let afterGeneration := steps input 2 warm
  let finalState := steps input 4 warm
  match afterGeneration.phase,finalState.phase,cold.phase with
  | .initializing _,.done fresh,.done old => decide (fresh.code = old.code ∧ fresh.loaded = old.loaded ∧ finalState.cache.current.tables = cold.cache.current.tables)
  | _,_,_ => false

-- The derived canonical root supplies the checked encoding and a concrete response.
/-- info: true -/
#guard_msgs in
#eval let input := request 7 3 2
  let finalState := steps input 6 {}
  match finished : finalState.phase with
  | .done result =>
    let root := NativeGoldBlockCodeBackend.planRoot input finalState (steps_reachable input 6 {} .initial) result finished
    let code := NativeGoldBlockCode.encoding result.code root
    NativeGoldRowEncoding.check code &&
      match NativeGoldRowEncoding.encodeResponses code 1 [1,2,3,4,5,6,7] with
      | none => false
      | some output => decide (output.length = 96)
  | _ => false

-- Completed objects remain unchanged when the constructor is ticked again.
/-- info: true -/
#guard_msgs in
#eval let input := request 1024 4 4
  let finalState := steps input 6 {}
  decide (steps input 3 finalState = finalState)

-- Complete serde bytes match independently checked native constructor fixtures.
/-- info: true -/
#guard_msgs in
#eval ([(1,1,2,[1,1,1,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0]),(7,3,2,[7,3,4,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0]),(1024,4,4,[251,0,4,4,251,0,1,251,0,4,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,207,200,161,29,128,180,83,6]),(4096,4,4,[251,0,16,4,251,0,4,251,0,16,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,151,121,209,53,35,239,68,21])] : List (Nat × Nat × Nat × List InputIndexedOracle.Byte)).all fun (m,b,e,bytes) =>
  match (steps (request m b e) 6 {}).phase with
  | .done result => decide (NativeGoldBlockCode.codec.encode result.code = bytes)
  | _ => false

end FormalProof4FHETest.HasteBootsNativeGoldBlockCodeBackendSmoke
