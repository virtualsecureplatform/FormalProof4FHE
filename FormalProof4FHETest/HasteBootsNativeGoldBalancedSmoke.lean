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

import all FormalProof4FHE.HasteBoots.NativeBrakedownParameters
import all FormalProof4FHE.HasteBoots.NativeGoldEncodedParameters
import all FormalProof4FHE.HasteBoots.NativeGoldParameterInitialization
import all FormalProof4FHE.HasteBoots.NativeGoldParameterStore
import all FormalProof4FHE.HasteBoots.NativeGoldConstructedRegistry

import all FormalProof4FHE.HasteBoots.NativeGoldBalancedLayout
import all FormalProof4FHE.HasteBoots.NativeGoldBalancedInitialization

namespace FormalProof4FHETest.HasteBootsNativeGoldBalancedSmoke
open FormalProof4FHE.HasteBoots
private def usize (n : Nat) : NativeUsizeMessage.Usize := Fin.ofNat (2^64) n
private def request (n w q b : Nat) : NativeGoldBalancedLayout.Request := ⟨usize n,usize w,usize q,usize b⟩
private def steps (input : NativeGoldBlockCodeProgram.Request) : Nat → NativeGoldBlockCodeProgram.Config → NativeGoldBlockCodeProgram.Config
  | 0,c => c
  | n+1,c => steps input n (NativeGoldBlockCodeProgram.tick input c)

-- The closed field characteristic uses nine bytes in the source score.
/-- info: true -/
#guard_msgs in
#eval ((NativeFields.goldilocksModulus.size+7)/8+1) == 9

/-- info: true -/
#guard_msgs in
#eval [(0,3,1,2,0,327),(2,4,1,2,0,624),(5,3,2,2,2,1464),
       (10,3,128,2,1,89344),(10,4,128,4,1,114688),(16,4,64,2,5,464896)].all fun (n,w,q,b,left,score) =>
  match NativeGoldBalancedLayout.select (request n w q b) with
  | .ok chosen => chosen.left == left && chosen.score == score
  | .error _ => false

/-- info: true -/
#guard_msgs in
#eval [(0,0,1,2,NativeGoldBalancedLayout.Error.dimensions),
       (0,1,0,2,.dimensions),(64,1,1,2,.dimensions),(0,1,1,1,.dimensions),
       (0,1,1,3,.dimensions),(63,2,1,2,.tableOverflow),
       (0,1,1,9223372036854775808,.unsupportedLayout)].all fun (n,w,q,b,expected) =>
  decide (NativeGoldBalancedLayout.select (request n w q b) = .error expected)

-- Incompatible domains and out-of-range row splits are skipped.
/-- info: true -/
#guard_msgs in
#eval (NativeGoldBalancedLayout.candidate (request 40 3 1 2) 0).isNone &&
  (NativeGoldBalancedLayout.candidate (request 5 3 2 2) 6).isNone

-- Two real globally minimal candidates tie; the first original split wins.
/-- info: true -/
#guard_msgs in
#eval let input := request 2 4 1 2
  match NativeGoldBalancedLayout.candidate input 0,NativeGoldBalancedLayout.candidate input 1 with
  | some first,some second => first.score == second.score &&
      decide (NativeGoldBalancedLayout.scan none [first,second] = some first) &&
      decide (NativeGoldBalancedLayout.scan none [second,first] = some second)
  | _,_ => false

-- The selected layout does not manufacture a completed code or parameter object.
/-- info: true -/
#guard_msgs in
#eval match NativeGoldBalancedInitialization.prepare (request 5 3 2 2) with
  | .ok prepared => (NativeGoldParameterInitialization.finish prepared.header ({} : NativeGoldBlockCodeProgram.Config)).isNone
  | .error _ => false

-- Full native code/context byte fixtures after the real word-model constructor.
/-- info: true -/
#guard_msgs in
#eval ([(0,3,1,2,[1,3,1,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0],[72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,0,3,0,1,3,32,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,1,3,1,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0]),(2,4,1,2,[4,4,1,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0],[72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,2,4,0,1,4,32,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,4,4,1,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0]),(5,3,2,2,[8,3,4,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0],[72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,5,3,2,2,3,32,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,8,3,4,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128,0,0,0]),(10,3,128,2,[251,0,2,3,251,0,1,251,0,2,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,114,217,254,139,215,42,143,157],[72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,10,3,1,128,3,251,0,2,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,251,0,2,3,251,0,1,251,0,2,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,114,217,254,139,215,42,143,157]),(10,4,128,4,[251,0,2,4,128,251,0,2,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,114,217,254,139,215,42,143,157],[72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,10,4,1,128,4,251,0,2,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,251,0,2,4,128,251,0,2,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,114,217,254,139,215,42,143,157]),(16,4,64,2,[251,0,8,4,251,0,2,251,0,4,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,207,200,161,29,128,180,83,6],[72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,16,4,5,64,4,251,0,4,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,251,0,8,4,251,0,2,251,0,4,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,207,200,161,29,128,180,83,6])] : List (Nat × Nat × Nat × Nat × List InputIndexedOracle.Byte × List InputIndexedOracle.Byte)).all fun (n,w,q,b,codeBytes,contextBytes) =>
  match NativeGoldBalancedInitialization.prepare (request n w q b) with
  | .error _ => false
  | .ok prepared =>
    let config := steps prepared.codeRequest 6 {}
    match NativeGoldParameterInitialization.finish prepared.header config with
    | some (.ok initialized) =>
      decide (NativeGoldBlockCode.codec.encode initialized.parameters.code = codeBytes) &&
      decide (NativeBrakedownContext.input NativeGoldBlockCode.description.row initialized.parameters = some contextBytes)
    | _ => false

end FormalProof4FHETest.HasteBootsNativeGoldBalancedSmoke
