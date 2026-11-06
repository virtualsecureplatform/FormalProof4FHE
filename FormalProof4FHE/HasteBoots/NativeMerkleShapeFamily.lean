module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchPaths
public import FormalProof4FHE.HasteBoots.NativeCanonicalLookupWire
public import FormalProof4FHE.HasteBoots.RecordRoots
@[expose] public section

/-! A fixed causal family of Merkle shapes, independent of context-hash
answers. Native checked allocation bounds cover every prepared batch height.
The family records an explicit 64 annotations per new key; this is a local
shape domain, not an attacker trial, history or lifetime bound. -/
namespace FormalProof4FHE.HasteBoots.NativeMerkleShapeFamily
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeGoldBatchPcsProgram (Context Prepared)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

abbrev Height := Fin 64
abbrev Tag := Digest × Height

def height (tag : Tag) : ℕ := tag.2.val
def shape (tag : Tag) : BinaryTree.Skeleton := .perfect (height tag)
def family (key : Source) : List (Tag × Digest) :=
  (List.finRange 64).map (fun index => ((key.1,index),key.2))
def requests (keys : List Source) : List (Tag × Digest) := keys.flatMap family

theorem family_length (key : Source) : (family key).length = 64 := by simp only [family,List.length_map,List.length_finRange]
theorem family_member (key : Source) (index : Height) : ((key.1,index),key.2) ∈ family key :=
  List.mem_map.mpr ⟨index,List.mem_finRange index,rfl⟩
theorem requests_member (keys : List Source) (key : Source) (member : key ∈ keys) (index : Height) :
    ((key.1,index),key.2) ∈ requests keys := List.mem_flatMap.mpr ⟨key,member,family_member key index⟩
theorem requests_length (keys : List Source) : (requests keys).length = keys.length*64 := by
  induction keys with
  | nil => rfl
  | cons key rest ih => simp only [requests,List.flatMap_cons,List.length_append,List.length_cons,family_length] at *; omega

theorem prepared_height (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) : work.geometry.height < 64 := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root
    ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have built := (NativeGoldBatchPrelude.sampling_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).1
  change geometry.height < 64
  have small := NativeBrakedownParameters.path_shift NativeGoldBlockCode.description ctx.parameters geometry built
  omega

def tag (context : Digest) (work : Prepared) : Tag := (context,Fin.ofNat 64 work.geometry.height)
theorem tag_height (context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) : height (tag context work) = work.geometry.height := by
  exact Nat.mod_eq_of_lt (prepared_height ctx world work executed)
end
end FormalProof4FHE.HasteBoots.NativeMerkleShapeFamily
