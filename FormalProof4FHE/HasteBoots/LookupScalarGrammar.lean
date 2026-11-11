module
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude
public import FormalProof4FHE.HasteBoots.ScalarLookupExpression
@[expose] public section

/-! Exact scalar equation slots from an actually completed native lookup
prelude. The original job/repetition selects its own public sum and identity
metadata, with grammar degrees derived from the literal native full test. -/
namespace FormalProof4FHE.HasteBoots.LookupScalarGrammar
open NativeSharedLookupStatement (Request Prepared)
open NativeScalarBatchWire (Info)
open NativeUsizeMessage (Usize)
open NativeFieldRepresentation (GoldWord)
open NativeGoldExtensionArithmetic (Word)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
noncomputable section

def sumInfo (n : Usize) : Info := ⟨⟨1,by decide⟩,n⟩
def identityInfo (n : Usize) (request : Request) : Info :=
  ⟨if request.terminal.logicalLength.val = 2^n.val then ⟨3,by decide⟩ else ⟨4,by decide⟩,n⟩

theorem sum_arity (n : Usize) (term : Unit) : ScalarLookupExpression.sumArity term ≤ (sumInfo n).maxMultiplicands.val := Nat.le_refl 1

theorem full_arity (n : Usize) (request : Request) (full : request.terminal.logicalLength.val = 2^n.val)
    (term : ExtensionLookupIdentity.FullTerm) :
    ExtensionLookupIdentity.fullArity term ≤ (identityInfo n request).maxMultiplicands.val := by
  simpa only [identityInfo,full,ite_true] using ExtensionLookupIdentity.full_degree term

theorem partial_arity (n : Usize) (request : Request) (partialPrefix : request.terminal.logicalLength.val ≠ 2^n.val)
    (term : ExtensionLookupIdentity.PartialTerm) :
    ExtensionLookupIdentity.partialArity term ≤ (identityInfo n request).maxMultiplicands.val := by
  simpa only [identityInfo,partialPrefix,ite_false] using ExtensionLookupIdentity.partial_degree term

/-- Exact original job slots, preserving repetition order. -/
theorem pairs_at (n : Usize) (jobs : List Prepared) (index : ℕ) (present : index < jobs.length) :
    (jobs.flatMap (fun job => NativeSharedLookupStatement.pair n job.tag.request))[2*index]? = some (sumInfo n) ∧
      (jobs.flatMap (fun job => NativeSharedLookupStatement.pair n job.tag.request))[2*index+1]? =
        some (identityInfo n (jobs[index]).tag.request) := by
  induction jobs generalizing index with
  | nil => simp only [List.length_nil] at present; omega
  | cons job tail ih =>
    cases index with
    | zero => exact ⟨rfl,rfl⟩
    | succ index =>
      have inside : index < tail.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using present
      simpa only [List.flatMap_cons,NativeSharedLookupStatement.pair,List.cons_append,List.nil_append,
        Nat.mul_succ,Nat.add_assoc,List.getElem?_cons_succ,List.getElem_cons_succ] using ih index inside

/-- One actual native prelude supplies both metadata slots and their exact
original initial claims. No separate job-order or statement certificate is
required, and multiplicities are read at the job's original request ordinal. -/
theorem protocol_pair {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) (n : Usize)
    (multiplicities : List (List GoldWord)) (roots : List Digest) (rootFits : roots.length < 2^64)
    (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World) (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (index : ℕ) (present : index < ready.jobs.length) :
    ready.statement.infos.val[2*index]? = some (sumInfo n) ∧
      ready.statement.infos.val[2*index+1]? = some (identityInfo n (ready.jobs[index]).tag.request) ∧
      ∃ counts, multiplicities[(ready.jobs[index]).tag.ordinal.val]? = some counts ∧
        ready.statement.claims.val[2*index]? =
          some (NativeGoldExtensionArithmetic.tableSum (ready.jobs[index]).output.inverses counts) ∧
        ready.statement.claims.val[2*index+1]? = some NativeGoldLookup.zero := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests n multiplicities roots rootFits
    w lookupFuel equalityFuel transcript world ready success
  have tags := (NativeSharedLookupPrepared.prepare_spec _ _ _ contract.prepared).1
  have built := NativeSharedLookupStatement.build_spec n (List.ofFn requests) ready.jobs multiplicities ready.statement contract.built
  have infos : ready.statement.infos.val = ready.jobs.flatMap (fun job => NativeSharedLookupStatement.pair n job.tag.request) := by
    rw [built.1,NativeSharedLookupStatement.infos_tags fits requests n,← tags,List.flatMap_map]
  obtain ⟨even,odd⟩ := pairs_at n ready.jobs index present
  rw [← infos] at even odd
  exact ⟨even,odd,NativeSharedLookupStatement.initialClaims_pair multiplicities ready.jobs ready.statement.claims.val built.2 index present⟩

end
end FormalProof4FHE.HasteBoots.LookupScalarGrammar
