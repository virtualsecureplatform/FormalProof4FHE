module
import all FormalProof4FHE.HasteBoots.StatementDerivedIdentityWork

namespace HasteBootsScalarStatementSizeSmoke
open FormalProof4FHE.HasteBoots
open NativeScalarBatchWire (Info Statement)
open NativeSharedLookupStatement (Request Prepared)
open NativePrefixCodec (Vector)

def largest : NativeFieldWire.GoldExtension := fun _ => ⟨2^64-1,by decide⟩

theorem raw_lazy_words_retained : (largest 0).val = 2^64-1 ∧
    NativeFields.goldilocksModulus ≤ (largest 0).val := by decide +kernel

theorem largest_extension_length : (NativeFieldWire.goldExtension largest).length = 28 := by decide +kernel

theorem zero_extension_length : (NativeFieldWire.goldExtension NativeGoldLookup.zero).length = 4 := by decide +kernel

def fullRequest : Request := ⟨1,[],1,⟨[0],⟨2^63,by decide⟩⟩⟩
def partialRequest : Request := ⟨1,[],1,⟨[0],⟨2^63-1,by decide⟩⟩⟩
def output : NativeGoldLookupProducer.Output :=
  ⟨NativeGoldLookup.zero,NativeGoldLookup.zero,[],NativeGoldLookup.zero,[],[]⟩
def jobs : List Prepared :=
  [⟨⟨⟨0,by decide⟩,0,fullRequest⟩,output⟩,⟨⟨⟨1,by decide⟩,0,partialRequest⟩,output⟩]
def statement : Statement :=
  ⟨⟨[⟨⟨1,by decide⟩,⟨63,by decide⟩⟩,⟨⟨3,by decide⟩,⟨63,by decide⟩⟩,
      ⟨⟨1,by decide⟩,⟨63,by decide⟩⟩,⟨⟨4,by decide⟩,⟨63,by decide⟩⟩],by decide⟩,
    ⟨List.replicate 4 NativeGoldLookup.zero,by decide⟩⟩

theorem built : NativeSharedLookupStatement.build ⟨63,by decide⟩ [fullRequest,partialRequest] jobs [[],[]] = some statement := by decide +kernel

theorem actual_degrees : statement.infos.val.map (fun info => info.maxMultiplicands.val) = [1,3,1,4] := by decide +kernel

theorem exact_statement_length : (NativeScalarBatchWire.statementCodec.encode statement).length = 26 := by decide +kernel

theorem constructed_length_bound : (NativeScalarBatchWire.statementCodec.encode statement).length ≤ 18+60*jobs.length :=
  CheckedScalarStatementSize.built_length _ _ _ _ _ built (by decide) (by decide +kernel)

def roots : Vector NativeRootMessage.Digest := ⟨[fun _ => 1,fun _ => 2],by decide⟩

theorem original_roots_pay : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit :=
  CheckedScalarStatementSize.fits_of_roots statement jobs roots constructed_length_bound rfl (by decide +kernel)

theorem missing_multiplicities_rejected :
    NativeSharedLookupStatement.build ⟨63,by decide⟩ [fullRequest,partialRequest] jobs [[]] = none := by decide +kernel

def widerInfo : Info := ⟨⟨4,by decide⟩,⟨251,by decide⟩⟩

theorem variable_count_changes_header : (NativeScalarBatchWire.infoCodec.encode widerInfo).length = 4 := by decide +kernel

end HasteBootsScalarStatementSizeSmoke
