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

namespace FormalProof4FHETest.HasteBootsNativeGoldParametersSmoke
open FormalProof4FHE.HasteBoots
private def usize (n : Nat) : NativeUsizeMessage.Usize := Fin.ofNat (2^64) n
private def request : NativeGoldBlockCodeProgram.Request := ⟨usize 8,usize 3,usize 2⟩
private def header : NativeGoldEncodedParameters.Header := ⟨usize 5,usize 3,usize 2,usize 2⟩
private def steps : Nat → NativeGoldBlockCodeProgram.Config → NativeGoldBlockCodeProgram.Config
  | 0,c => c
  | n+1,c => steps n (NativeGoldBlockCodeProgram.tick request c)
private def completed := steps 6 {}

/-- info: true -/
#guard_msgs in
#eval match NativeGoldParameterInitialization.finish header completed with
  | some (.ok initialized) =>
    initialized.parameters.numVariables.val == 5 && initialized.parameters.width.val == 3 &&
    initialized.parameters.code.messageLength.val == 8 && initialized.parameters.code.blocks.val == 32
  | _ => false

/-- info: true -/
#guard_msgs in
#eval (NativeGoldParameterInitialization.finish header ({} : NativeGoldBlockCodeProgram.Config)).isNone

/-- info: true -/
#guard_msgs in
#eval match completed.phase with
  | .done result =>
    [(0,0,0,1,NativeGoldEncodedParameters.Error.dimensions),
     (5,3,6,1,.dimensions), (64,3,0,1,.dimensions), (5,3,2,0,.dimensions),
     (5,3,1,2,.codeShape)].all fun (n,w,l,q,expected) =>
      match NativeGoldEncodedParameters.build ⟨usize n,usize w,usize l,usize q⟩ result.code with
      | .error actual => decide (actual = expected)
      | .ok _ => false
  | _ => false

-- Accessor-level overflow checks. The huge-tree object is deliberately not
-- claimed reachable from the block-code constructor, matching Rust's RowCode fixture.
/-- info: true -/
#guard_msgs in
#eval match completed.phase with
  | .done result =>
    let small := {result.code with messageLength := usize 1, blockWidth := usize 1, messageBlocks := usize 1}
    [(63,2,63,32,NativeGoldEncodedParameters.Error.tableOverflow),
     (63,1,63,32,.encodedOverflow), (0,4294967296,0,32,.linearOverflow),
     (0,1,0,9223372036854775808,.merkleOverflow)].all fun (n,w,l,b,expected) =>
      match NativeGoldEncodedParameters.build ⟨usize n,usize w,usize l,usize 1⟩ {small with blocks := usize b} with
      | .error actual => decide (actual = expected)
      | .ok _ => false
  | _ => false

-- Arena aliases retain each original slot and the supplied commitment roots.
/-- info: true -/
#guard_msgs in
#eval match NativeGoldParameterStore.allocate [] request header completed with
  | some (.ok first) =>
    match NativeGoldParameterStore.allocate first.entries request header completed with
    | some (.ok second) =>
      let root : NativeRootMessage.Digest := fun _ => 7
      match NativeGoldParameterStore.collect second.entries [⟨0,root⟩,⟨1,root⟩,⟨0,root⟩] with
      | some values => first.handle == 0 && second.handle == 1 && values.length == 3 &&
          values.all (fun oracle => oracle.parameters.code.messageLength.val == 8)
      | none => false
    | _ => false
  | _ => false

/-- info: true -/
#guard_msgs in
#eval (NativeGoldParameterStore.collect [] [⟨0,fun _ => 7⟩]).isNone

end FormalProof4FHETest.HasteBootsNativeGoldParametersSmoke
