module

public import FormalProof4FHE.HasteBoots.NativeGoldCoefficientsQuery
public import FormalProof4FHE.HasteBoots.NativeLookupRequestWire
public import FormalProof4FHE.HasteBoots.NativeByteCodec

@[expose] public section

/-!
# Native Brakedown matrix-query and opening-claim payloads

Matrices serialize width then a raw-word vector; a pair serializes zero
then one. The local extension post-map is deliberately absent from the PCS
query. Vector/usize domains describe constructed native allocations, not
strict proof decoding or an adversary-work bound.
-/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsWire

open NativeUsizeMessage (Usize)
open NativeLookupRequestWire (Row rowCodec)
open NativePrefixCodec (Codec product transport vector usize)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)

structure Matrix where
  width : Usize
  values : Row
  deriving DecidableEq

abbrev Pair := Matrix × Matrix
abbrev Query := NativePrefixCodec.Vector Pair

def matrixEquiv : (Usize × Row) ≃ Matrix where
  toFun := fun pair => ⟨pair.1,pair.2⟩
  invFun := fun matrix => ⟨matrix.width,matrix.values⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def matrixCodec : Codec Matrix := transport (product usize rowCodec) matrixEquiv

def pairCodec : Codec Pair := product matrixCodec matrixCodec

def queryCodec : Codec Query := vector pairCodec

def Matrix.model (matrix : Matrix) : NativeGoldMatrix.Matrix := ⟨matrix.width.val,matrix.values.val⟩
def pairModel (pair : Pair) : NativeGoldCoefficientsQuery.Pair := ⟨pair.1.model,pair.2.model⟩
def Query.models (query : Query) : List NativeGoldCoefficientsQuery.Pair := query.val.map pairModel

def Fits (matrix : NativeGoldMatrix.Matrix) : Prop := matrix.width < 2^64 ∧ matrix.values.length < 2^64
instance (matrix : NativeGoldMatrix.Matrix) : Decidable (Fits matrix) := inferInstanceAs (Decidable (_ ∧ _))

def fromMatrix (matrix : NativeGoldMatrix.Matrix) (fits : Fits matrix) : Matrix :=
  ⟨⟨matrix.width,fits.1⟩,⟨matrix.values,fits.2⟩⟩

def pairFits (pair : NativeGoldCoefficientsQuery.Pair) : Prop := Fits pair.zero ∧ Fits pair.one
instance (pair : NativeGoldCoefficientsQuery.Pair) : Decidable (pairFits pair) := inferInstanceAs (Decidable (_ ∧ _))

def fromPairs (pairs : List NativeGoldCoefficientsQuery.Pair) : Option Query :=
  if count : pairs.length < 2^64 then
    if fits : ∀ pair ∈ pairs, pairFits pair then
      some ⟨pairs.attach.map (fun pair =>
        (fromMatrix pair.val.zero (fits pair.val pair.property).1,fromMatrix pair.val.one (fits pair.val pair.property).2)),by
          rw [List.length_map,List.length_attach]; exact count⟩
    else none
  else none

theorem matrix_model (matrix : NativeGoldMatrix.Matrix) (fits : Fits matrix) : (fromMatrix matrix fits).model = matrix := rfl

theorem valid_fits (matrix : NativeGoldMatrix.Matrix) (width : ℕ) (valid : NativeGoldMatrix.validate matrix width = true) : Fits matrix := by
  have shape := (NativeGoldMatrix.validate_iff matrix width).mp valid
  have small : width < 2^64 := by nlinarith [shape.2.2.1]
  exact ⟨shape.2.1 ▸ small,shape.2.2.2 ▸ shape.2.2.1⟩

theorem fromPairs_spec (pairs : List NativeGoldCoefficientsQuery.Pair) (query : Query) (success : fromPairs pairs = some query) : query.models = pairs := by
  unfold fromPairs at success
  split at success
  next count =>
    split at success
    next fits =>
      have same := Option.some.inj success
      subst query
      simp only [Query.models,List.map_map,Function.comp_def,pairModel,matrix_model,List.attach_map_subtype_val]
    next rejected => contradiction
  next rejected => contradiction

theorem fromPairs_complete (pairs : List NativeGoldCoefficientsQuery.Pair) (count : pairs.length < 2^64)
    (fits : ∀ pair ∈ pairs, pairFits pair) : ∃ query, fromPairs pairs = some query := by
  unfold fromPairs
  rw [dite_eq_left count,dite_eq_left fits]
  exact ⟨_,rfl⟩

/-- Only the PCS query is packed; the caller-local extension post-map is not serialized. -/
def coefficientsQuery (width : ℕ) (point : List NativeGoldExtensionArithmetic.Word) : Option Query :=
  (NativeGoldCoefficientsQuery.coefficientsQuery width point).bind (fun query => fromPairs query.pairs)

theorem coefficientsQuery_complete (width : ℕ) (point : List NativeGoldExtensionArithmetic.Word)
    (shape : NativeGoldProjection.dimensions width = true) (count : point.length < 2^64) :
    ∃ query, coefficientsQuery width point = some query ∧ query.models = (NativeGoldCoefficientsQuery.built width point).pairs := by
  have fits : ∀ pair ∈ (NativeGoldCoefficientsQuery.built width point).pairs, pairFits pair := by
    intro pair member
    obtain ⟨value,_,same⟩ := List.mem_map.mp member
    subst pair
    exact ⟨valid_fits _ width (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape),
      valid_fits _ width (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape)⟩
  obtain ⟨query,packed⟩ := fromPairs_complete _ (by rw [NativeGoldCoefficientsQuery.built_length]; exact count) fits
  refine ⟨query,?_,fromPairs_spec _ _ packed⟩
  simp only [coefficientsQuery,NativeGoldCoefficientsQuery.coefficientsQuery_success _ _ shape,Option.bind_some,packed]

theorem coefficientsQuery_models (width : ℕ) (point : List NativeGoldExtensionArithmetic.Word) (query : Query)
    (shape : NativeGoldProjection.dimensions width = true) (success : coefficientsQuery width point = some query) :
    query.models = (NativeGoldCoefficientsQuery.built width point).pairs := by
  simp only [coefficientsQuery,NativeGoldCoefficientsQuery.coefficientsQuery_success _ _ shape,Option.bind_some] at success
  exact fromPairs_spec _ _ success

theorem matrix_encode (matrix : Matrix) : matrixCodec.encode matrix = NativeUsizeMessage.encode matrix.width ++ rowCodec.encode matrix.values := rfl

theorem pair_encode (pair : Pair) : pairCodec.encode pair = matrixCodec.encode pair.1 ++ matrixCodec.encode pair.2 := rfl

theorem query_encode (query : Query) : queryCodec.encode query = NativeUsizeMessage.encode ⟨query.val.length,query.property⟩ ++
    query.val.flatMap (fun pair => matrixCodec.encode pair.1 ++ matrixCodec.encode pair.2) := rfl

theorem query_prefix (query : Query) (suffix : Input) : queryCodec.read (queryCodec.encode query ++ suffix) = some (query,suffix) := queryCodec.read_encode _ _

def openingCodec : Codec (Digest × Query × Row) := product NativeByteCodec.digest (product queryCodec rowCodec)

def opening (root : Digest) (query : Query) (values : Row) : Input := openingCodec.encode (root,query,values)

theorem opening_encode (root : Digest) (query : Query) (values : Row) : opening root query values =
    List.ofFn root ++ queryCodec.encode query ++ rowCodec.encode values := by
  simp only [opening,openingCodec,product,NativeByteCodec.digest_encode,List.append_assoc]

theorem opening_prefix (root : Digest) (query : Query) (values : Row) (suffix : Input) :
    openingCodec.read (opening root query values ++ suffix) = some ((root,query,values),suffix) := openingCodec.read_encode _ _

theorem opening_injective (left right : Digest × Query × Row) (same : openingCodec.encode left = openingCodec.encode right) : left = right := openingCodec.encode_injective same

def claimCodec : Codec (Usize × Usize × Query × Row) := product usize (product usize (product queryCodec rowCodec))

def claim (ordinal slot : Usize) (query : Query) (values : Row) : Input := claimCodec.encode (ordinal,slot,query,values)

theorem claim_encode (ordinal slot : Usize) (query : Query) (values : Row) : claim ordinal slot query values =
    NativeUsizeMessage.encode ordinal ++ NativeUsizeMessage.encode slot ++ queryCodec.encode query ++ rowCodec.encode values := by
  simp only [claim,claimCodec,product,NativePrefixCodec.usize,List.append_assoc]

theorem claim_prefix (ordinal slot : Usize) (query : Query) (values : Row) (suffix : Input) :
    claimCodec.read (claim ordinal slot query values ++ suffix) = some ((ordinal,slot,query,values),suffix) := claimCodec.read_encode _ _

end FormalProof4FHE.HasteBoots.NativeGoldPcsWire
