module
import all FormalProof4FHE.HasteBoots.NativeGoldLookupSourceInvariant
import all FormalProof4FHETest.HasteBootsDeferredRegistrySmoke
open FormalProof4FHE.HasteBoots
open OracleProgram (run)
open HasteBootsRegistryAncestrySmoke (usize digest root description registry world)
open HasteBootsDeferredRegistrySmoke (initial query values allRequests collected)
namespace HasteBootsSourceInvariantSmoke
noncomputable section

def final := (collected allRequests values).1.progress
private def isDone : NativeSharedSourceClaims.Result → Bool
  | .done _ => true
  | .stopped _ _ => false
private theorem accepted : (collected allRequests values).1 = .done final := by
  have done : isDone (collected allRequests values).1 = true := by decide +kernel
  cases found : (collected allRequests values).1 with
  | done progress => simp only [final,found,NativeSharedSourceClaims.Result.progress]
  | stopped progress reason => simp only [found,isDone,Bool.false_eq_true] at done

-- These instantiate the general proofs on a successful lazy-alias run.
example : NativeSourceClaimInvariant.Unique final :=
  (NativeSourceClaimInvariant.program_invariants description registry allRequests query values initial world rfl).1
example : NativeSourceClaimInvariant.Recorded query final :=
  (NativeSourceClaimInvariant.program_invariants description registry allRequests query values initial world rfl).2.1
example : final.state.claims.val.length = final.seen.length ∧ final.seen.length ≤ registry.val.length :=
  NativeSourceClaimInvariant.program_counts description registry allRequests query values initial world rfl
example : final.seen.Pairwise (fun left right => left.slot < right.slot) :=
  NativeSourceClaimInvariant.program_order description registry allRequests query values initial world rfl
example : NativeSourceClaimDomain.Available (collected allRequests values).1 :=
  NativeSourceClaimDomain.program_available description registry allRequests query values initial world rfl rfl (by decide)

-- Context/root equality chooses the first USED slot 0, not its lazy alias 1.
example (previous : NativeSharedSourceClaims.Seen) (member : previous ∈ final.seen) (key : previous.key = (digest 0,root)) : previous.slot = 0 := by
  have context : (run (NativeBrakedownContext.context description (registry.val.get ⟨0,by decide⟩).parameters) world).run.1 = some previous.key.1 := by
    rw [key]
    decide +kernel
  have rootSame : (registry.val.get ⟨0,by decide⟩).root = previous.key.2 := by rw [key]; rfl
  have bound := NativeSourceClaimInvariant.program_first_used description registry allRequests query values initial world rfl final accepted
    previous member ⟨0,by decide⟩ (by decide +kernel) context rootSame
  exact Nat.eq_zero_of_le_zero bound

-- Alias slot 1 is covered through an earlier representative with field-equal values.
example : ∃ digest row previous,
    (run (NativeBrakedownContext.context description (registry.val.get ⟨1,by decide⟩).parameters) world).run.1 = some digest ∧
    values.val[1]? = some row ∧ previous ∈ final.seen ∧ previous.key = (digest,(registry.val.get ⟨1,by decide⟩).root) ∧
    NativeGoldPcsClaim.equal previous.values.val row.val = true ∧ previous.slot ≤ 1 :=
  NativeSourceClaimInvariant.program_covers description registry allRequests query values initial world final accepted ⟨1,by decide⟩ (by decide +kernel)

def word : NativeGoldExtensionArithmetic.Word := fun index => usize (index.val+1)
def pulled := NativeGoldScalarQuery.scalarQuery 1 4 [word,word,word]
def packed := pulled.bind (fun query => NativeGoldPcsWire.fromPairs query.pairs)
example : packed.map (fun query => query.val.length) = some 1 := by decide +kernel
example : pulled.map (fun query => query.post.isNone) = some true := by decide +kernel
example : (NativeGoldScalarQuery.scalarQuery 1 4 [word,word]).isNone = true := by decide +kernel
example : (NativeGoldScalarQuery.scalarQuery 1 3 [word,word,word]).isNone = true := by decide +kernel
example : (NativeGoldScalarQuery.scalarQuery (2^64-2) 4 []).isNone = true := by decide +kernel

-- A local lane post-map is retained by scalar checking and omitted by PCS packing.
def onlyPost := NativeGoldScalarQuery.scalarQuery 0 4 [word,word]
example : onlyPost.map (fun query => query.post.isSome) = some true := by decide +kernel
example : (onlyPost.bind (fun query => NativeGoldPcsWire.fromPairs query.pairs)).map (fun query => query.val.length) = some 0 := by decide +kernel

-- A genuine alias rejection still satisfies the proved indexing/allocation domain.
example : NativeSourceClaimDomain.Available (collected allRequests HasteBootsDeferredRegistrySmoke.badValues).1 :=
  NativeSourceClaimDomain.program_available description registry allRequests query HasteBootsDeferredRegistrySmoke.badValues initial world rfl rfl (by decide)

-- Earlier UNUSED slot 0 remains the dispatch owner, while slot 1 owns this claim.
example : ((collected HasteBootsRegistryAncestrySmoke.requests values).1.progress.seen.map NativeSharedSourceClaims.Seen.slot) = [1] := by decide +kernel

-- Explicit complete-key collisions are allowed by this deterministic layer.
-- Initialization and collection use the SAME world and therefore merge all aliases.
def collisionWorld : InputIndexedOracle.World := fun _ => 0
def collisionProgram := OracleProgram.bind
  (NativeSourceRegistry.startRegistry description registry HasteBootsRegistryAncestrySmoke.parent)
  (fun metadata => match metadata with
    | none => .pure none
    | some metadata => OracleProgram.bind
        (NativeSharedSourceClaims.program description registry allRequests query values (NativeDeferredOpeningBatch.initial metadata))
        (fun result => .pure (some result)))
def collision := (run collisionProgram collisionWorld).run
example : collision.1.map (fun result => result.progress.seen.map NativeSharedSourceClaims.Seen.slot) = some [0] := by decide +kernel
example : collision.1.map (fun result => result.progress.state.claims.val.map (fun claim => claim.slot.val)) = some [0] := by decide +kernel
example : collision.2.length = 6 := by decide +kernel

end
end HasteBootsSourceInvariantSmoke
