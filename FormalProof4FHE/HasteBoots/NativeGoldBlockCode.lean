module

public import FormalProof4FHE.HasteBoots.NativeBrakedownParameters
public import FormalProof4FHE.HasteBoots.NativeGoldRowEncoding
public import FormalProof4FHE.HasteBoots.NativeFieldWire
public import Mathlib.Data.Nat.Size
import all Init.Data.String.Defs

@[expose] public section

/-! Retained Goldilocks BlockReedSolomonCode fields and constructor arithmetic.
Table generation, initialization and loading remain explicit backend calls.
Their results contain raw roots, never encoder-correctness certificates.
This is a functional source model, not a Rust/cache refinement theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBlockCode

open NativeUsizeMessage (Usize)
open NativeFieldRepresentation (GoldWord)
open InputIndexedOracle (Input Byte)

structure Stored where
  messageLength : Usize
  blockWidth : Usize
  messageBlocks : Usize
  blocks : Usize
  modulus : NativePrefixCodec.Vector Byte
  domainRoot : GoldWord
  deriving DecidableEq

abbrev Fields := Usize × Usize × Usize × Usize × NativePrefixCodec.Vector Byte × GoldWord

def fields : Stored ≃ Fields where
  toFun code := (code.messageLength,code.blockWidth,code.messageBlocks,code.blocks,code.modulus,code.domainRoot)
  invFun tuple := ⟨tuple.1,tuple.2.1,tuple.2.2.1,tuple.2.2.2.1,tuple.2.2.2.2.1,tuple.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serde struct fields have declaration order and no struct header. -/
def codec : NativePrefixCodec.Codec Stored :=
  NativePrefixCodec.transport
    (NativePrefixCodec.product NativePrefixCodec.usize
      (NativePrefixCodec.product NativePrefixCodec.usize
        (NativePrefixCodec.product NativePrefixCodec.usize
          (NativePrefixCodec.product NativePrefixCodec.usize
            (NativePrefixCodec.product NativeByteCodec.bytes NativePrefixCodec.usize))))) fields.symm

theorem serialize_fields (code : Stored) : codec.encode code =
    NativeUsizeMessage.encode code.messageLength ++
      (NativeUsizeMessage.encode code.blockWidth ++
        (NativeUsizeMessage.encode code.messageBlocks ++
          (NativeUsizeMessage.encode code.blocks ++
            (NativeByteCodec.bytes.encode code.modulus ++ NativeFieldWire.gold code.domainRoot)))) := rfl

theorem serialize_prefix (code : Stored) (suffix : Input) :
    codec.read (codec.encode code ++ suffix) = some (code,suffix) := codec.read_encode _ _

theorem serialize_injective : Function.Injective codec.encode := codec.encode_injective

def domain : NativePrefixCodec.Vector Byte :=
  ⟨NativeTranscript.utf8 "block-rs/negacyclic-ntt/v1",by decide +kernel⟩

/-- Accessors and complete serialized bytes all come from the same retained object. -/
def description : NativeBrakedownParameters.Description Stored where
  messageLength := Stored.messageLength
  row := ⟨Stored.blockWidth,Stored.blocks,fun _ => domain,fun code => some (codec.encode code)⟩

/-- Rust div_ceil without a potentially overflowing numerator addition. -/
def ceilBlocks (message block : ℕ) : ℕ := message/block + if message%block = 0 then 0 else 1

def nextLog (count : ℕ) : ℕ := (count-1).size
def paddedBlocks (message block : ℕ) : ℕ := 2^(nextLog (ceilBlocks message block))
def domainBlocks (message block blowup : ℕ) : ℕ := max (paddedBlocks message block*blowup) 32
def logSize (code : Stored) : ℕ := code.blocks.val.size-1

/-- Observable backend calls at the constructor boundary. Cache state and
the implementation that computes these responses are separate obligations. -/
structure Tables where
  generate : ℕ → Bool
  initTable : ℕ → Bool
  load : ℕ → Option NativeGoldSolinas.Word

inductive Error where
  | dimensions | messageOverflow | domainOverflow | codewordOverflow
  | generation | initialization | loading
  deriving DecidableEq

def build (tables : Tables) (message block blowup : Usize) : Except Error Stored :=
  if valid : message.val ≠ 0 ∧ block.val ≠ 0 ∧ 2 ≤ blowup.val ∧ blowup.val = 2^(nextLog blowup.val) then
    let padded := paddedBlocks message.val block.val
    if fitsMessage : padded < 2^64 then
      if padded*blowup.val < 2^64 then
        let count := domainBlocks message.val block.val blowup.val
        if fitsCode : count*block.val < 2^64 then
          have fitsCount : count < 2^64 := by
            have blockPositive : 0 < block.val := Nat.pos_of_ne_zero valid.2.1
            nlinarith
          let exponent := count.size-1
          if tables.generate exponent then
            if tables.initTable exponent then
              match tables.load exponent with
              | none => .error .loading
              | some root => .ok ⟨message,block,⟨padded,fitsMessage⟩,⟨count,fitsCount⟩,
                  NativeBrakedownContext.modulus,NativeGoldSolinas.raw root⟩
            else .error .initialization
          else .error .generation
        else .error .codewordOverflow
      else .error .domainOverflow
    else .error .messageOverflow
  else .error .dimensions

/-- Encoding uses the retained root and an actual loaded plan root. -/
def encoding (code : Stored) (planRoot : NativeGoldSolinas.Word) : NativeGoldRowEncoding.Code :=
  ⟨code.messageLength.val,code.blockWidth.val,logSize code,code.domainRoot,planRoot⟩

structure Spec (tables : Tables) (message block blowup : Usize) (code : Stored) : Prop where
  dimensions : message.val ≠ 0 ∧ block.val ≠ 0 ∧ 2 ≤ blowup.val ∧ blowup.val = 2^(nextLog blowup.val)
  messageFits : paddedBlocks message.val block.val < 2^64
  domainFits : paddedBlocks message.val block.val*blowup.val < 2^64
  strideFits : domainBlocks message.val block.val blowup.val*block.val < 2^64
  messageEq : code.messageLength = message
  blockEq : code.blockWidth = block
  padded : code.messageBlocks.val = paddedBlocks message.val block.val
  count : code.blocks.val = domainBlocks message.val block.val blowup.val
  modulus : code.modulus = NativeBrakedownContext.modulus
  generated : tables.generate (logSize code) = true
  initialized : tables.initTable (logSize code) = true
  loaded : ∃ root, tables.load (logSize code) = some root ∧ code.domainRoot = NativeGoldSolinas.raw root

theorem build_spec (tables : Tables) (message block blowup : Usize) (code : Stored)
    (success : build tables message block blowup = .ok code) : Spec tables message block blowup code := by
  unfold build at success
  split at success
  next valid =>
    dsimp only at success
    split at success
    next fitsMessage =>
      split at success
      next fitsDomain =>
        split at success
        next fitsCode =>
          split at success
          next generated =>
            split at success
            next initialized =>
              split at success
              next => contradiction
              next root loaded =>
                cases success
                exact ⟨valid,fitsMessage,fitsDomain,fitsCode,rfl,rfl,rfl,rfl,rfl,generated,initialized,root,loaded,rfl⟩
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

end FormalProof4FHE.HasteBoots.NativeGoldBlockCode
