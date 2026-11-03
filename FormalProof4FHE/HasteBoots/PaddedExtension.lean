module

public import FormalProof4FHE.HasteBoots.MatrixFold
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Padded extension coefficients and native multiplication matrices

The packing width is d+padding, where d is the extension basis dimension.
Encoding appends zeros; decoding ignores those lanes. Their composite on base
vectors is a projection, not an identity. Native matrix columns are the encoded
products a*basis[column], with unused columns zero. They implement E*(a·)*D
on arbitrary vectors, without assuming original committed padding is zero.
The concrete native polynomial basis/field, machine dimensions and Rust/byte
refinement remain separate from these generic field identities.
-/

open scoped BigOperators Classical
open Matrix

namespace FormalProof4FHE.HasteBoots.PaddedExtension

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d padding : ℕ}

def encode (basis : Module.Basis (Fin d) F K) : K →ₗ[F] (Fin (d + padding) → F) where
  toFun value := Fin.addCases (basis.equivFun value) (fun _ => 0)
  map_add' first second := by
    funext lane
    refine Fin.addCases (fun i => ?_) (fun i => ?_) lane <;> simp
  map_smul' coefficient value := by
    funext lane
    refine Fin.addCases (fun i => ?_) (fun i => ?_) lane <;> simp

def decode (basis : Module.Basis (Fin d) F K) : (Fin (d + padding) → F) →ₗ[F] K where
  toFun values := basis.equivFun.symm (fun i => values (i.castAdd padding))
  map_add' first second := by rw [← map_add]; rfl
  map_smul' coefficient values := by rw [← map_smul]; rfl

theorem encode_left (basis : Module.Basis (Fin d) F K) (value : K) (i : Fin d) :
    encode (padding := padding) basis value (i.castAdd padding) = basis.equivFun value i := by simp [encode]

theorem encode_right (basis : Module.Basis (Fin d) F K) (value : K) (i : Fin padding) :
    encode basis value (Fin.natAdd d i) = 0 := by simp [encode]

theorem decode_encode (basis : Module.Basis (Fin d) F K) (value : K) :
    decode (padding := padding) basis (encode basis value) = value := by
  simp [decode, encode]

theorem decode_sum (basis : Module.Basis (Fin d) F K) (values : Fin (d + padding) → F) :
    decode basis values = ∑ i : Fin d, values (i.castAdd padding) • basis i :=
  basis.equivFun_symm_apply _

def Padded (values : Fin (d + padding) → F) : Prop := ∀ i : Fin padding, values (Fin.natAdd d i) = 0

theorem encode_padded (basis : Module.Basis (Fin d) F K) (value : K) : Padded (encode (padding := padding) basis value) :=
  encode_right basis value

theorem encode_decode_left (basis : Module.Basis (Fin d) F K) (values : Fin (d + padding) → F) (i : Fin d) :
    encode basis (decode basis values) (i.castAdd padding) = values (i.castAdd padding) := by
  rw [encode_left]
  change (basis.equivFun (basis.equivFun.symm (fun j => values (j.castAdd padding)))) i = values (i.castAdd padding)
  rw [LinearEquiv.apply_symm_apply]

theorem encode_decode_iff (basis : Module.Basis (Fin d) F K) (values : Fin (d + padding) → F) :
    encode basis (decode basis values) = values ↔ Padded values := by
  constructor
  · intro equal i
    have entry := congrFun equal (Fin.natAdd d i)
    simpa only [encode_right] using entry.symm
  · intro padded
    funext lane
    refine Fin.addCases (fun i => ?_) (fun i => ?_) lane
    · exact encode_decode_left basis values i
    · rw [encode_right, padded i]

def element (basis : Module.Basis (Fin d) F K) (values : Fin (d + padding) → F) : Option K :=
  if Padded values then some (decode basis values) else none

theorem element_encode (basis : Module.Basis (Fin d) F K) (value : K) :
    element basis (encode (padding := padding) basis value) = some value := by
  rw [element, ite_eq_left (encode_padded basis value), decode_encode]

theorem element_some_iff (basis : Module.Basis (Fin d) F K) (values : Fin (d + padding) → F) (value : K) :
    element basis values = some value ↔ values = encode basis value := by
  constructor
  · intro accepted
    have padded : Padded values := by
      by_contra wrong
      simp [element, wrong] at accepted
    have equal : decode basis values = value := by simpa [element, padded] using accepted
    exact ((encode_decode_iff basis values).mpr padded).symm.trans (congrArg (encode basis) equal)
  · intro equal
    rw [equal, element_encode]

def multiplication (basis : Module.Basis (Fin d) F K) (value : K) :
    Matrix (Fin (d + padding)) (Fin (d + padding)) F := fun row =>
  Fin.addCases (fun column => encode basis (value * basis column) row) (fun _ => 0)

theorem multiplication_left (basis : Module.Basis (Fin d) F K) (value : K) (row : Fin (d + padding)) (column : Fin d) :
    multiplication basis value row (column.castAdd padding) = encode basis (value * basis column) row := by
  simp [multiplication]

theorem multiplication_right (basis : Module.Basis (Fin d) F K) (value : K) (row : Fin (d + padding)) (column : Fin padding) :
    multiplication basis value row (Fin.natAdd d column) = 0 := by simp [multiplication]

/-- Column-loop matrix semantics on arbitrary raw committed vectors. -/
theorem multiplication_mulVec (basis : Module.Basis (Fin d) F K) (value : K) (values : Fin (d + padding) → F) :
    multiplication basis value *ᵥ values = encode basis (value * decode basis values) := by
  funext row
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, multiplication_left, multiplication_right,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [decode_sum, Finset.mul_sum]
  simp only [mul_smul_comm, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem multiplication_encode (basis : Module.Basis (Fin d) F K) (value input : K) :
    multiplication (padding := padding) basis value *ᵥ encode basis input = encode basis (value * input) := by
  rw [multiplication_mulVec, decode_encode]

theorem multiplication_mul (basis : Module.Basis (Fin d) F K) (first second : K) :
    multiplication (padding := padding) basis first * multiplication basis second = multiplication basis (first * second) := by
  apply Matrix.mulVec_injective
  funext values
  rw [← Matrix.mulVec_mulVec, multiplication_mulVec, multiplication_mulVec, decode_encode, multiplication_mulVec, mul_assoc]

theorem projection_mulVec (basis : Module.Basis (Fin d) F K) (values : Fin (d + padding) → F) :
    multiplication basis 1 *ᵥ values = encode basis (decode basis values) := by
  rw [multiplication_mulVec, one_mul]

theorem projection_idempotent (basis : Module.Basis (Fin d) F K) :
    multiplication (padding := padding) basis 1 * multiplication basis 1 = multiplication basis 1 := by
  rw [multiplication_mul, one_mul]

theorem element_multiplication (basis : Module.Basis (Fin d) F K) (value : K) (values : Fin (d + padding) → F) :
    element basis (multiplication basis value *ᵥ values) = some (value * decode basis values) := by
  rw [multiplication_mulVec, element_encode]

end

end FormalProof4FHE.HasteBoots.PaddedExtension
