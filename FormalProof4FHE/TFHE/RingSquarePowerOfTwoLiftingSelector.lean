/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.RankBound
import FormalProof4FHE.Probability.FiniteSurjectiveFiber
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.TFHE.RingSquareBinaryPreimageExistence

/-!
# Power-of-Two Lifting Selectors for `RGSW_S(-S)`

For coefficient modulus `2^k`, random binary subset sum has additional structure that is absent
for a generic finite group.  One can solve the lowest bit by linear algebra over `ZMod 2`, combine
disjoint nonempty parity-kernel subsets, divide their sums by two, and recurse at modulus
`2^(k-1)`.

This file starts with the deterministic algebraic core of that construction.  The source masks
are split into a prefix and disjoint blocks.  A prefix solution fixes the target parity; one
parity-zero subset in each block becomes a mask for the next layer.  Any solution at the lower
layer then expands to a binary solution at the upper layer.  The construction uses exactly

`c 0 = N + s`, `c (d+1) = (N+s) + (N+1)c d`

source masks for `d+1` lifting steps.  For fixed modulus exponent this is polynomial in the ring
degree and rank slack.  Subsequent sections connect the deterministic theorem to uniform masks
and the finite-field rank-failure bound.
-/

open scoped BigOperators
open scoped ENNReal

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting

noncomputable section

open FormalProof4FHE.LeftoverHash
open OracleComp

/-! ## Source-count recurrence -/

/-- Number of non-anchor masks used by the recursive lifting construction.  `depth = 0` is the
single parity layer (coefficient modulus two); every successor adds one two-adic layer. -/
def sourceCount (depth degree slack : ℕ) : ℕ :=
  Nat.rec (degree + slack)
    (fun _ lowerCount ↦ (degree + slack) + (degree + 1) * lowerCount)
    depth

@[simp]
theorem sourceCount_zero (degree slack : ℕ) :
    sourceCount 0 degree slack = degree + slack := rfl

@[simp]
theorem sourceCount_succ (depth degree slack : ℕ) :
    sourceCount (depth + 1) degree slack =
      (degree + slack) + (degree + 1) * sourceCount depth degree slack := by
  rfl

/-- Convenient polynomial bound when the two-adic depth is fixed. -/
theorem sourceCount_le_depth_mul_power (depth degree slack : ℕ) :
    sourceCount depth degree slack ≤
      (depth + 1) * (degree + slack) * (degree + 1) ^ depth := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      rw [sourceCount_succ]
      calc
        (degree + slack) + (degree + 1) * sourceCount depth degree slack ≤
            (degree + slack) + (degree + 1) *
              ((depth + 1) * (degree + slack) * (degree + 1) ^ depth) := by
          gcongr
        _ = (degree + slack) +
              (depth + 1) * (degree + slack) * (degree + 1) ^ (depth + 1) := by
          rw [pow_succ]
          ring
        _ ≤ (degree + slack) * (degree + 1) ^ (depth + 1) +
              (depth + 1) * (degree + slack) * (degree + 1) ^ (depth + 1) := by
          apply Nat.add_le_add_right
          calc
            degree + slack = (degree + slack) * 1 := by simp
            _ ≤ (degree + slack) * (degree + 1) ^ (depth + 1) :=
              Nat.mul_le_mul_left _ (Nat.one_le_pow' (depth + 1) degree)
        _ = (depth + 1 + 1) * (degree + slack) *
              (degree + 1) ^ (depth + 1) := by ring

/-! ## Generic exact two-adic layer -/

/-- Algebra needed for one lifting step.  `parity` extracts the low layer, `double` embeds the
next lower layer as the parity-zero subgroup, and `half` is a chosen inverse on that subgroup. -/
structure ExactTwoLayer (Upper Lower Parity : Type)
    [AddCommGroup Upper] [AddCommGroup Lower] [AddCommGroup Parity] where
  parity : Upper →+ Parity
  double : Lower →+ Upper
  half : Upper → Lower
  double_half_of_parity_zero : ∀ value, parity value = 0 →
    double (half value) = value

/-- Additive maps commute with binary subset sums. -/
theorem map_binarySubsetSum
    {Index G H : Type} [Fintype Index] [DecidableEq Index]
    [AddCommMonoid G] [AddCommMonoid H]
    (hom : G →+ H) (table : Index → G) (bits : Index → Bool) :
    hom (binarySubsetSum table bits) =
      binarySubsetSum (hom ∘ table) bits := by
  unfold binarySubsetSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hbit : bits index
  · simp [hbit]
  · simp [Bool.eq_false_of_not_eq_true hbit]

/-- A surjective additive map sends a uniform finite-group sample to a uniform sample. -/
theorem evalDist_map_surjective_addHom_uniform
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain] [SampleableType Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    [SampleableType Codomain]
    (transform : Domain →+ Codomain) (hsurjective : Function.Surjective transform) :
    evalDist (transform <$> ($ᵗ Domain)) = evalDist ($ᵗ Codomain) := by
  classical
  apply evalDist_ext
  intro output
  rw [probOutput_uniformSample Codomain output,
    probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample Domain]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfiber :
      (Finset.univ.filter fun input : Domain ↦ output = transform input).card =
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
    rw [show (Finset.univ.filter fun input : Domain ↦ output = transform input) =
        Finset.univ.filter fun input : Domain ↦ transform input = output by
      ext input
      simp [eq_comm]]
    exact AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (hsurjective output)) (Set.mem_range.2 (hsurjective 0))
  rw [hfiber]
  let zeroFiber :=
    (Finset.univ.filter fun input : Domain ↦ transform input = 0).card
  have hzeroFiberPos : 0 < zeroFiber := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hcardNat : zeroFiber * Fintype.card Codomain = Fintype.card Domain := by
    exact
      FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
        transform hsurjective
  have hcard :
      (zeroFiber : ℝ≥0∞) * (Fintype.card Codomain : ℝ≥0∞) =
        (Fintype.card Domain : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  change (zeroFiber : ℝ≥0∞) * (Fintype.card Domain : ℝ≥0∞)⁻¹ = _
  rw [← hcard]
  have hinv :
      ((zeroFiber : ℝ≥0∞) * (Fintype.card Codomain : ℝ≥0∞))⁻¹ =
        (zeroFiber : ℝ≥0∞)⁻¹ * (Fintype.card Codomain : ℝ≥0∞)⁻¹ :=
    ENNReal.mul_inv
      (Or.inr (ENNReal.natCast_ne_top (Fintype.card Codomain)))
      (Or.inl (ENNReal.natCast_ne_top zeroFiber))
  rw [hinv]
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr hzeroFiberPos.ne')
    (ENNReal.natCast_ne_top zeroFiber), one_mul]

/-- Binary subset summation as an additive homomorphism in the public table. -/
def binarySubsetSumAddHom
    {Index G : Type} [Fintype Index] [DecidableEq Index] [AddCommGroup G]
    (bits : Index → Bool) : (Index → G) →+ G where
  toFun table := binarySubsetSum table bits
  map_zero' := by simp [binarySubsetSum]
  map_add' left right := by
    unfold binarySubsetSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    cases bits index <;> simp

/-- A binary subset-sum map is surjective as soon as at least one bit is selected. -/
theorem binarySubsetSumAddHom_surjective
    {Index G : Type} [Fintype Index] [DecidableEq Index] [AddCommGroup G]
    (bits : Index → Bool) (selected : Index) (hselected : bits selected = true) :
    Function.Surjective (binarySubsetSumAddHom (G := G) bits) := by
  intro target
  let table : Index → G := fun index ↦ if index = selected then target else 0
  refine ⟨table, ?_⟩
  change binarySubsetSum table bits = target
  unfold binarySubsetSum
  rw [Finset.sum_eq_single selected]
  · simp [table, hselected]
  · intro index _ hne
    simp [table, hne]
  · simp

/-- Therefore a nonempty fixed subset of a uniform additive table has an exactly uniform sum. -/
theorem evalDist_binarySubsetSum_uniform
    {Index G : Type} [Fintype Index] [DecidableEq Index]
    [AddCommGroup G] [Fintype G] [DecidableEq G] [SampleableType G]
    [SampleableType (Index → G)]
    (bits : Index → Bool) (selected : Index) (hselected : bits selected = true) :
    evalDist (binarySubsetSumAddHom (G := G) bits <$> ($ᵗ (Index → G))) =
      evalDist ($ᵗ G) :=
  evalDist_map_surjective_addHom_uniform
    (binarySubsetSumAddHom (G := G) bits)
    (binarySubsetSumAddHom_surjective bits selected hselected)

/-- Apply one binary subset sum independently in each disjoint block. -/
def blockBinarySubsetSumAddHom
    {Block Item G : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Item] [DecidableEq Item] [AddCommGroup G]
    (bits : Block → Item → Bool) :
    (Block × Item → G) →+ (Block → G) where
  toFun table block :=
    binarySubsetSum (fun item ↦ table (block, item)) (bits block)
  map_zero' := by
    funext block
    simp [binarySubsetSum]
  map_add' left right := by
    funext block
    exact map_add (binarySubsetSumAddHom (G := G) (bits block))
      (fun item ↦ left (block, item)) (fun item ↦ right (block, item))

/-- Disjoint block summation is jointly surjective when every block subset is nonempty. -/
theorem blockBinarySubsetSumAddHom_surjective
    {Block Item G : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Item] [DecidableEq Item] [AddCommGroup G]
    (bits : Block → Item → Bool)
    (selected : Block → Item)
    (hselected : ∀ block, bits block (selected block) = true) :
    Function.Surjective (blockBinarySubsetSumAddHom (G := G) bits) := by
  intro target
  choose rows hrows using fun block ↦
    binarySubsetSumAddHom_surjective (G := G) (bits block)
      (selected block) (hselected block) (target block)
  refine ⟨fun pair ↦ rows pair.1 pair.2, ?_⟩
  funext block
  exact hrows block

/-- A bit vector distinct from the all-false vector contains a selected coordinate. -/
theorem exists_true_of_ne_allFalse {Index : Type} (bits : Index → Bool)
    (hnonzero : bits ≠ fun _ ↦ false) : ∃ index, bits index = true := by
  classical
  by_contra hnone
  apply hnonzero
  funext index
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact hnone ⟨index, htrue⟩

/-- A canonical selected coordinate from a nonzero bit vector. -/
noncomputable def selectedTrue {Index : Type} (bits : Index → Bool)
    (hnonzero : bits ≠ fun _ ↦ false) : Index :=
  (exists_true_of_ne_allFalse bits hnonzero).choose

theorem selectedTrue_spec {Index : Type} (bits : Index → Bool)
    (hnonzero : bits ≠ fun _ ↦ false) :
    bits (selectedTrue bits hnonzero) = true :=
  (exists_true_of_ne_allFalse bits hnonzero).choose_spec

/-- Index layout for one lifting step: a parity-solving prefix followed by disjoint blocks. -/
abbrev LayerIndex (prefixCount blockCount lowerCount : ℕ) :=
  Fin prefixCount ⊕ (Fin lowerCount × Fin blockCount)

def prefixMasks {Upper : Type} {prefixCount blockCount lowerCount : ℕ}
    (masks : LayerIndex prefixCount blockCount lowerCount → Upper) :
    Fin prefixCount → Upper :=
  fun index ↦ masks (Sum.inl index)

def blockMasks {Upper : Type} {prefixCount blockCount lowerCount : ℕ}
    (masks : LayerIndex prefixCount blockCount lowerCount → Upper)
    (lowerIndex : Fin lowerCount) : Fin blockCount → Upper :=
  fun blockIndex ↦ masks (Sum.inr (lowerIndex, blockIndex))

/-- Expand prefix bits, one kernel vector per block, and lower-layer bits to all upper masks. -/
def liftBits {prefixCount blockCount lowerCount : ℕ}
    (prefixBits : Fin prefixCount → Bool)
    (kernelBits : Fin lowerCount → Fin blockCount → Bool)
    (lowerBits : Fin lowerCount → Bool) :
    LayerIndex prefixCount blockCount lowerCount → Bool
  | Sum.inl index => prefixBits index
  | Sum.inr pair => lowerBits pair.1 && kernelBits pair.1 pair.2

/-- Sum selected inside one disjoint block. -/
def blockSubsetSum
    {Upper : Type} [AddCommMonoid Upper]
    {prefixCount blockCount lowerCount : ℕ}
    (masks : LayerIndex prefixCount blockCount lowerCount → Upper)
    (kernelBits : Fin lowerCount → Fin blockCount → Bool)
    (lowerIndex : Fin lowerCount) : Upper :=
  binarySubsetSum (blockMasks masks lowerIndex) (kernelBits lowerIndex)

/-- Masks passed to the next layer after taking half of each parity-zero block sum. -/
def compressedMasks
    {Upper Lower Parity : Type}
    [AddCommGroup Upper] [AddCommGroup Lower] [AddCommGroup Parity]
    (tower : ExactTwoLayer Upper Lower Parity)
    {prefixCount blockCount lowerCount : ℕ}
    (masks : LayerIndex prefixCount blockCount lowerCount → Upper)
    (kernelBits : Fin lowerCount → Fin blockCount → Bool) :
    Fin lowerCount → Lower :=
  fun lowerIndex ↦ tower.half (blockSubsetSum masks kernelBits lowerIndex)

/-- The expanded bit vector sums to the prefix contribution plus the selected whole block sums. -/
theorem binarySubsetSum_liftBits
    {Upper : Type} [AddCommMonoid Upper]
    {prefixCount blockCount lowerCount : ℕ}
    (masks : LayerIndex prefixCount blockCount lowerCount → Upper)
    (prefixBits : Fin prefixCount → Bool)
    (kernelBits : Fin lowerCount → Fin blockCount → Bool)
    (lowerBits : Fin lowerCount → Bool) :
    binarySubsetSum masks (liftBits prefixBits kernelBits lowerBits) =
      binarySubsetSum (prefixMasks masks) prefixBits +
        binarySubsetSum (blockSubsetSum masks kernelBits) lowerBits := by
  classical
  unfold binarySubsetSum prefixMasks blockSubsetSum blockMasks liftBits
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro lowerIndex _
  by_cases hlower : lowerBits lowerIndex
  · simp [hlower, binarySubsetSum]
  · have hlowerFalse : lowerBits lowerIndex = false :=
      Bool.eq_false_of_not_eq_true hlower
    simp [hlowerFalse]

/-- One deterministic lifting step.  A parity-correct prefix and parity-zero block kernels make
the residual divisible by two.  Any lower-layer subset-sum solution then expands to an exact
upper-layer solution. -/
theorem binarySubsetSum_liftBits_eq_target
    {Upper Lower Parity : Type}
    [AddCommGroup Upper] [AddCommGroup Lower] [AddCommGroup Parity]
    (tower : ExactTwoLayer Upper Lower Parity)
    {prefixCount blockCount lowerCount : ℕ}
    (masks : LayerIndex prefixCount blockCount lowerCount → Upper)
    (target : Upper)
    (prefixBits : Fin prefixCount → Bool)
    (kernelBits : Fin lowerCount → Fin blockCount → Bool)
    (lowerBits : Fin lowerCount → Bool)
    (hPrefix :
      binarySubsetSum (tower.parity ∘ prefixMasks masks) prefixBits =
        tower.parity target)
    (hKernel : ∀ lowerIndex,
      binarySubsetSum
          (tower.parity ∘ blockMasks masks lowerIndex)
          (kernelBits lowerIndex) = 0)
    (hLower :
      binarySubsetSum (compressedMasks tower masks kernelBits) lowerBits =
        tower.half (target - binarySubsetSum (prefixMasks masks) prefixBits)) :
    binarySubsetSum masks (liftBits prefixBits kernelBits lowerBits) = target := by
  let prefixSum := binarySubsetSum (prefixMasks masks) prefixBits
  let blockSum := blockSubsetSum masks kernelBits
  have hPrefixParity : tower.parity prefixSum = tower.parity target := by
    rw [map_binarySubsetSum]
    exact hPrefix
  have hResidualParity : tower.parity (target - prefixSum) = 0 := by
    rw [map_sub, hPrefixParity, sub_self]
  have hBlockParity : ∀ lowerIndex, tower.parity (blockSum lowerIndex) = 0 := by
    intro lowerIndex
    dsimp [blockSum, blockSubsetSum]
    rw [map_binarySubsetSum]
    exact hKernel lowerIndex
  have hDoubleCompressed : ∀ lowerIndex,
      tower.double ((compressedMasks tower masks kernelBits) lowerIndex) =
        blockSum lowerIndex := by
    intro lowerIndex
    exact tower.double_half_of_parity_zero _ (hBlockParity lowerIndex)
  have hDoubleLower :
      tower.double
          (binarySubsetSum (compressedMasks tower masks kernelBits) lowerBits) =
        binarySubsetSum blockSum lowerBits := by
    rw [map_binarySubsetSum]
    apply congrArg (fun table ↦ binarySubsetSum table lowerBits)
    funext lowerIndex
    exact hDoubleCompressed lowerIndex
  have hBlockSum :
      binarySubsetSum blockSum lowerBits = target - prefixSum := by
    rw [← hDoubleLower, hLower]
    exact tower.double_half_of_parity_zero _ hResidualParity
  rw [binarySubsetSum_liftBits]
  change prefixSum + binarySubsetSum blockSum lowerBits = target
  rw [hBlockSum, add_sub_cancel]

/-! ## The coefficientwise `ZMod (2^(k+1))` tower -/

/-- Additive embedding of `ZMod (2^k)` as the even residues of `ZMod (2^(k+1))`. -/
def scalarDouble (exponent : ℕ) :
    ZMod (2 ^ exponent) →+ ZMod (2 ^ (exponent + 1)) :=
  ZMod.lift (2 ^ exponent) ⟨
    (AddMonoidHom.mulLeft (2 : ZMod (2 ^ (exponent + 1)))).comp
      (Int.castAddHom (ZMod (2 ^ (exponent + 1)))),
    by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft,
        Int.coe_castAddHom]
      rw [Int.cast_natCast]
      change (2 : ZMod (2 ^ (exponent + 1))) *
        ((2 ^ exponent : ℕ) : ZMod (2 ^ (exponent + 1))) = 0
      rw [show (2 : ZMod (2 ^ (exponent + 1))) =
          ((2 : ℕ) : ZMod (2 ^ (exponent + 1))) by rfl]
      rw [← Nat.cast_mul]
      rw [show 2 * 2 ^ exponent = 2 ^ (exponent + 1) by
        rw [pow_succ]
        omega]
      exact ZMod.natCast_self _
  ⟩

/-- Coefficient parity from one two-adic layer to `ZMod 2`. -/
def scalarParity (exponent : ℕ) :
    ZMod (2 ^ (exponent + 1)) →+ ZMod 2 :=
  (ZMod.castHom (pow_dvd_pow 2 (by omega : 1 ≤ exponent + 1)) (ZMod 2)).toAddMonoidHom

/-- Canonical integer-representative halving.  It is used only when parity is zero. -/
def scalarHalf (exponent : ℕ) (value : ZMod (2 ^ (exponent + 1))) :
    ZMod (2 ^ exponent) :=
  (value.val / 2 : ℕ)

@[simp]
theorem scalarDouble_intCast (exponent : ℕ) (value : ℤ) :
    scalarDouble exponent (value : ZMod (2 ^ exponent)) =
      (2 * value : ℤ) := by
  unfold scalarDouble
  rw [ZMod.lift_coe]
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft,
    Int.coe_castAddHom, Int.cast_mul, Int.cast_ofNat]

@[simp]
theorem scalarDouble_natCast (exponent value : ℕ) :
    scalarDouble exponent (value : ZMod (2 ^ exponent)) =
      (2 * value : ℕ) := by
  exact_mod_cast scalarDouble_intCast exponent (value : ℤ)

/-- Halving is a right inverse to doubling on every even residue. -/
theorem scalarDouble_half_of_parity_zero
    (exponent : ℕ) (value : ZMod (2 ^ (exponent + 1)))
    (hParity : scalarParity exponent value = 0) :
    scalarDouble exponent (scalarHalf exponent value) = value := by
  have valueEven : 2 ∣ value.val := by
    change ZMod.castHom (pow_dvd_pow 2 (by omega : 1 ≤ exponent + 1))
        (ZMod 2) value = 0 at hParity
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hParity
    exact (CharP.cast_eq_zero_iff (ZMod 2) 2 value.val).mp hParity
  obtain ⟨half, hhalf⟩ := valueEven
  rw [show scalarHalf exponent value = (half : ZMod (2 ^ exponent)) by
    unfold scalarHalf
    congr 1
    omega]
  rw [scalarDouble_natCast]
  simpa [hhalf] using ZMod.natCast_zmod_val value

@[simp]
private theorem finEquiv_symm_val (modulus : ℕ) [NeZero modulus]
    (value : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm value).val = value.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl

private theorem finEquiv_apply_eq_natCast (modulus : ℕ) [NeZero modulus]
    (value : Fin modulus) :
    ZMod.finEquiv modulus value = (value.val : ZMod modulus) := by
  cases modulus with
  | zero => exact Fin.elim0 value
  | succ modulus => exact (Fin.cast_val_eq_self value).symm

/-- Split a residue modulo `2^(k+1)` into its low bit and its `k` high bits. -/
def scalarSplitEquiv (exponent : ℕ) :
    ZMod (2 ^ (exponent + 1)) ≃ ZMod 2 × ZMod (2 ^ exponent) :=
  ((ZMod.finEquiv (2 ^ (exponent + 1))).toEquiv.symm.trans
      (finCongr (pow_succ 2 exponent))).trans
    (((finProdFinEquiv.symm.trans
      (Equiv.prodCongr
        (ZMod.finEquiv (2 ^ exponent)).toEquiv
        (ZMod.finEquiv 2).toEquiv))).trans
      (Equiv.prodComm (ZMod (2 ^ exponent)) (ZMod 2)))

/-- The abstract split equivalence computes the same parity and representative half used by the
lifting tower. -/
theorem scalarSplitEquiv_apply (exponent : ℕ)
    (value : ZMod (2 ^ (exponent + 1))) :
    scalarSplitEquiv exponent value =
      (scalarParity exponent value, scalarHalf exponent value) := by
  let index : Fin (2 ^ exponent * 2) :=
    finCongr (pow_succ 2 exponent)
      ((ZMod.finEquiv (2 ^ (exponent + 1))).symm value)
  have hindex : index.val = value.val := by
    simp [index]
  apply Prod.ext
  · change ZMod.finEquiv 2 index.modNat = scalarParity exponent value
    rw [finEquiv_apply_eq_natCast]
    change ((index.val % 2 : ℕ) : ZMod 2) = scalarParity exponent value
    rw [hindex]
    change _ = ZMod.castHom (pow_dvd_pow 2 (by omega : 1 ≤ exponent + 1))
      (ZMod 2) value
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact ZMod.natCast_mod value.val 2
  · change ZMod.finEquiv (2 ^ exponent) index.divNat = scalarHalf exponent value
    rw [finEquiv_apply_eq_natCast]
    change ((index.val / 2 : ℕ) : ZMod (2 ^ exponent)) = _
    rw [hindex]
    rfl

/-- Recombination is the usual low-bit plus twice-the-high-part formula. -/
theorem scalarSplitEquiv_symm_apply (exponent : ℕ)
    (parity : ZMod 2) (high : ZMod (2 ^ exponent)) :
    (scalarSplitEquiv exponent).symm (parity, high) =
      (parity.val + 2 * high.val : ℕ) := by
  apply (scalarSplitEquiv exponent).injective
  rw [(scalarSplitEquiv exponent).apply_symm_apply,
    scalarSplitEquiv_apply]
  have hbound : parity.val + 2 * high.val < 2 ^ (exponent + 1) := by
    rw [pow_succ]
    have hparity := parity.val_lt
    have hhigh := high.val_lt
    omega
  apply Prod.ext
  · change parity = scalarParity exponent
      (parity.val + 2 * high.val : ℕ)
    symm
    change ZMod.castHom (pow_dvd_pow 2 (by omega : 1 ≤ exponent + 1))
      (ZMod 2) (parity.val + 2 * high.val : ℕ) = parity
    rw [map_natCast, Nat.cast_add, Nat.cast_mul]
    rw [show ((2 : ℕ) : ZMod 2) = 0 by exact ZMod.natCast_self 2,
      zero_mul, add_zero]
    exact ZMod.natCast_zmod_val parity
  · change high = scalarHalf exponent
      (parity.val + 2 * high.val : ℕ)
    unfold scalarHalf
    rw [ZMod.val_natCast_of_lt hbound]
    have hdiv : (parity.val + 2 * high.val) / 2 = high.val := by
      have hparity := parity.val_lt
      omega
    rw [hdiv]
    exact (ZMod.natCast_zmod_val high).symm

/-- Holding the low bit fixed, changing the high part adds an embedded even residue. -/
theorem scalarSplitEquiv_symm_eq_base_add_double (exponent : ℕ)
    (parity : ZMod 2) (high : ZMod (2 ^ exponent)) :
    (scalarSplitEquiv exponent).symm (parity, high) =
      (scalarSplitEquiv exponent).symm (parity, 0) + scalarDouble exponent high := by
  have hdouble : scalarDouble exponent high = (2 * high.val : ℕ) := by
    calc
      scalarDouble exponent high =
          scalarDouble exponent (high.val : ZMod (2 ^ exponent)) := by
            rw [ZMod.natCast_zmod_val]
      _ = (2 * high.val : ℕ) := scalarDouble_natCast exponent high.val
  rw [scalarSplitEquiv_symm_apply, scalarSplitEquiv_symm_apply, hdouble]
  simp only [ZMod.val_zero, mul_zero, add_zero]
  push_cast
  ring

@[simp]
theorem scalarHalf_double (exponent : ℕ) (value : ZMod (2 ^ exponent)) :
    scalarHalf exponent (scalarDouble exponent value) = value := by
  rw [← ZMod.natCast_zmod_val value, scalarDouble_natCast]
  unfold scalarHalf
  have hbound : 2 * value.val < 2 ^ (exponent + 1) := by
    rw [pow_succ]
    simpa [Nat.mul_comm] using
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 value.val_lt
  rw [ZMod.val_natCast_of_lt hbound]
  simp

theorem scalarDouble_injective (exponent : ℕ) :
    Function.Injective (scalarDouble exponent) := by
  intro left right heq
  have := congrArg (scalarHalf exponent) heq
  simpa using this

/-- Coefficient vectors at one modulus layer. -/
abbrev CoefficientVector (exponent degree : ℕ) :=
  Fin degree → ZMod (2 ^ exponent)

/-- Coefficientwise parity map on a polynomial vector. -/
def coefficientParity (exponent degree : ℕ) :
    CoefficientVector (exponent + 1) degree →+
      CoefficientVector 1 degree where
  toFun value := fun coefficient ↦ scalarParity exponent (value coefficient)
  map_zero' := by funext coefficient; simp [scalarParity]
  map_add' left right := by
    funext coefficient
    exact map_add (scalarParity exponent) (left coefficient) (right coefficient)

/-- Coefficientwise even-residue embedding. -/
def coefficientDouble (exponent degree : ℕ) :
    CoefficientVector exponent degree →+
      CoefficientVector (exponent + 1) degree where
  toFun value := fun coefficient ↦ scalarDouble exponent (value coefficient)
  map_zero' := by funext coefficient; simp
  map_add' left right := by
    funext coefficient
    exact map_add (scalarDouble exponent) (left coefficient) (right coefficient)

/-- Coefficientwise representative halving. -/
def coefficientHalf (exponent degree : ℕ)
    (value : CoefficientVector (exponent + 1) degree) :
    CoefficientVector exponent degree :=
  fun coefficient ↦ scalarHalf exponent (value coefficient)

/-- Coefficientwise low/high-bit decomposition. -/
def coefficientSplitEquiv (exponent degree : ℕ) :
    CoefficientVector (exponent + 1) degree ≃
      CoefficientVector 1 degree × CoefficientVector exponent degree where
  toFun value :=
    (coefficientParity exponent degree value, coefficientHalf exponent degree value)
  invFun split := fun coefficient ↦
    (scalarSplitEquiv exponent).symm (split.1 coefficient, split.2 coefficient)
  left_inv value := by
    funext coefficient
    apply (scalarSplitEquiv exponent).injective
    calc
      scalarSplitEquiv exponent
          ((scalarSplitEquiv exponent).symm
            ((coefficientParity exponent degree) value coefficient,
              coefficientHalf exponent degree value coefficient)) =
          ((coefficientParity exponent degree) value coefficient,
            coefficientHalf exponent degree value coefficient) :=
        (scalarSplitEquiv exponent).apply_symm_apply _
      _ = scalarSplitEquiv exponent (value coefficient) := by
        rw [scalarSplitEquiv_apply]
        rfl
  right_inv split := by
    apply Prod.ext <;> funext coefficient
    · change scalarParity exponent
        ((scalarSplitEquiv exponent).symm
          (split.1 coefficient, split.2 coefficient)) = split.1 coefficient
      have hinverse := (scalarSplitEquiv exponent).apply_symm_apply
        (split.1 coefficient, split.2 coefficient)
      exact congrArg Prod.fst
        ((scalarSplitEquiv_apply exponent _).symm.trans hinverse)
    · change scalarHalf exponent
        ((scalarSplitEquiv exponent).symm
          (split.1 coefficient, split.2 coefficient)) = split.2 coefficient
      have hinverse := (scalarSplitEquiv exponent).apply_symm_apply
        (split.1 coefficient, split.2 coefficient)
      exact congrArg Prod.snd
        ((scalarSplitEquiv_apply exponent _).symm.trans hinverse)

/-- Split every entry of a coefficient-vector table into its parity and high tables. -/
def coefficientTableSplitEquiv (Index : Type) (exponent degree : ℕ) :
    (Index → CoefficientVector (exponent + 1) degree) ≃
      (Index → CoefficientVector 1 degree) ×
        (Index → CoefficientVector exponent degree) where
  toFun table :=
    (fun index ↦ (coefficientSplitEquiv exponent degree (table index)).1,
      fun index ↦ (coefficientSplitEquiv exponent degree (table index)).2)
  invFun split := fun index ↦
    (coefficientSplitEquiv exponent degree).symm
      (split.1 index, split.2 index)
  left_inv table := by
    funext index
    exact (coefficientSplitEquiv exponent degree).symm_apply_apply (table index)
  right_inv split := by
    apply Prod.ext <;> funext index
    · exact congrArg Prod.fst
        ((coefficientSplitEquiv exponent degree).apply_symm_apply
          (split.1 index, split.2 index))
    · exact congrArg Prod.snd
        ((coefficientSplitEquiv exponent degree).apply_symm_apply
          (split.1 index, split.2 index))

/-- Apply coefficient parity to every entry of a table as an additive homomorphism. -/
def coefficientParityTableAddHom (Index : Type) (exponent degree : ℕ) :
    (Index → CoefficientVector (exponent + 1) degree) →+
      (Index → CoefficientVector 1 degree) where
  toFun table := (coefficientParity exponent degree) ∘ table
  map_zero' := by
    funext index
    simp
  map_add' left right := by
    funext index
    exact map_add (coefficientParity exponent degree) (left index) (right index)

theorem coefficientParityTableAddHom_surjective (Index : Type)
    (exponent degree : ℕ) :
    Function.Surjective (coefficientParityTableAddHom Index exponent degree) := by
  intro target
  refine ⟨fun index ↦ (coefficientSplitEquiv exponent degree).symm
    (target index, 0), ?_⟩
  funext index
  have hinverse := (coefficientSplitEquiv exponent degree).apply_symm_apply
    (target index, (0 : CoefficientVector exponent degree))
  exact congrArg Prod.fst hinverse

/-- Hence coefficient parity maps a uniform upper table to a uniform parity table. -/
theorem coefficientParityTable_uniform_evalDist
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (exponent degree : ℕ) :
    evalDist
        (coefficientParityTableAddHom Index exponent degree <$>
          ($ᵗ (Index → CoefficientVector (exponent + 1) degree))) =
      evalDist ($ᵗ (Index → CoefficientVector 1 degree)) :=
  evalDist_map_surjective_addHom_uniform
    (coefficientParityTableAddHom Index exponent degree)
    (coefficientParityTableAddHom_surjective Index exponent degree)

@[simp]
theorem coefficientHalf_double (exponent degree : ℕ)
    (value : CoefficientVector exponent degree) :
    coefficientHalf exponent degree (coefficientDouble exponent degree value) = value := by
  funext coefficient
  exact scalarHalf_double exponent (value coefficient)

theorem coefficientDouble_injective (exponent degree : ℕ) :
    Function.Injective (coefficientDouble exponent degree) := by
  intro left right heq
  have := congrArg (coefficientHalf exponent degree) heq
  simpa using this

/-- Recombining a fixed parity vector with a high vector is its zero-high representative plus
the coefficientwise doubled high vector. -/
theorem coefficientSplitEquiv_symm_eq_base_add_double
    (exponent degree : ℕ)
    (parity : CoefficientVector 1 degree)
    (high : CoefficientVector exponent degree) :
    (coefficientSplitEquiv exponent degree).symm (parity, high) =
      (coefficientSplitEquiv exponent degree).symm (parity, 0) +
        coefficientDouble exponent degree high := by
  funext coefficient
  exact scalarSplitEquiv_symm_eq_base_add_double exponent
    (parity coefficient) (high coefficient)

/-- Binary subset summation distributes over pointwise table addition. -/
theorem binarySubsetSum_add_tables
    {Index G : Type} [Fintype Index] [DecidableEq Index] [AddCommGroup G]
    (left right : Index → G) (bits : Index → Bool) :
    binarySubsetSum (left + right) bits =
      binarySubsetSum left bits + binarySubsetSum right bits :=
  map_add (binarySubsetSumAddHom (G := G) bits) left right

/-- Join parity and high tables coefficientwise. -/
def joinCoefficientMasks {Index : Type} (exponent degree : ℕ)
    (parities : Index → CoefficientVector 1 degree)
    (highs : Index → CoefficientVector exponent degree) :
    Index → CoefficientVector (exponent + 1) degree :=
  fun index ↦ (coefficientSplitEquiv exponent degree).symm
    (parities index, highs index)

@[simp]
theorem coefficientParity_joinCoefficientMasks
    {Index : Type} (exponent degree : ℕ)
    (parities : Index → CoefficientVector 1 degree)
    (highs : Index → CoefficientVector exponent degree)
    (index : Index) :
    coefficientParity exponent degree
      (joinCoefficientMasks exponent degree parities highs index) = parities index := by
  have hinverse := (coefficientSplitEquiv exponent degree).apply_symm_apply
    (parities index, highs index)
  exact congrArg Prod.fst hinverse

/-- A joined subset sum is a fixed parity representative plus the doubled high-part subset sum. -/
theorem binarySubsetSum_joinCoefficientMasks
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (exponent degree : ℕ)
    (parities : Index → CoefficientVector 1 degree)
    (highs : Index → CoefficientVector exponent degree)
    (bits : Index → Bool) :
    binarySubsetSum (joinCoefficientMasks exponent degree parities highs) bits =
      binarySubsetSum (joinCoefficientMasks exponent degree parities 0) bits +
        coefficientDouble exponent degree (binarySubsetSum highs bits) := by
  have htable : joinCoefficientMasks exponent degree parities highs =
      joinCoefficientMasks exponent degree parities 0 +
        (coefficientDouble exponent degree) ∘ highs := by
    funext index
    exact coefficientSplitEquiv_symm_eq_base_add_double exponent degree
      (parities index) (highs index)
  rw [htable, binarySubsetSum_add_tables, map_binarySubsetSum]

/-- Once the selected parity sum is zero, compression is an affine translate of the high-part
binary subset sum. -/
theorem coefficientHalf_binarySubsetSum_joinCoefficientMasks
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (exponent degree : ℕ)
    (parities : Index → CoefficientVector 1 degree)
    (highs : Index → CoefficientVector exponent degree)
    (bits : Index → Bool)
    (hParity : binarySubsetSum parities bits = 0) :
    coefficientHalf exponent degree
        (binarySubsetSum (joinCoefficientMasks exponent degree parities highs) bits) =
      coefficientHalf exponent degree
          (binarySubsetSum (joinCoefficientMasks exponent degree parities 0) bits) +
        binarySubsetSum highs bits := by
  let baseSum :=
    binarySubsetSum (joinCoefficientMasks exponent degree parities 0) bits
  have hBaseParity : coefficientParity exponent degree baseSum = 0 := by
    rw [map_binarySubsetSum]
    have htable :
        (coefficientParity exponent degree) ∘
            joinCoefficientMasks exponent degree parities 0 = parities := by
      funext index
      exact coefficientParity_joinCoefficientMasks exponent degree parities 0 index
    rw [htable, hParity]
  have hBaseDouble :
      coefficientDouble exponent degree
          (coefficientHalf exponent degree baseSum) = baseSum :=
    by
      funext coefficient
      apply scalarDouble_half_of_parity_zero
      exact congrFun hBaseParity coefficient
  rw [binarySubsetSum_joinCoefficientMasks]
  change coefficientHalf exponent degree
      (baseSum + coefficientDouble exponent degree (binarySubsetSum highs bits)) = _
  rw [← hBaseDouble, ← map_add, coefficientHalf_double]

/-- Compress every disjoint block after fixing all of its parity coefficients. -/
def fixedParityCompressed
    {Block Item : Type} [Fintype Item] [DecidableEq Item]
    (exponent degree : ℕ)
    (parities : Block × Item → CoefficientVector 1 degree)
    (bits : Block → Item → Bool)
    (highs : Block × Item → CoefficientVector exponent degree) :
    Block → CoefficientVector exponent degree :=
  fun block ↦ coefficientHalf exponent degree
    (binarySubsetSum
      (joinCoefficientMasks exponent degree
        (fun item ↦ parities (block, item))
        (fun item ↦ highs (block, item)))
      (bits block))

/-- Conditional on the parity table, block compression is a jointly surjective additive map of
the high table followed by a fixed translation. -/
theorem fixedParityCompressed_eq_blockSum_add_offset
    {Block Item : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Item] [DecidableEq Item]
    (exponent degree : ℕ)
    (parities : Block × Item → CoefficientVector 1 degree)
    (bits : Block → Item → Bool)
    (hParity : ∀ block,
      binarySubsetSum (fun item ↦ parities (block, item)) (bits block) = 0)
    (highs : Block × Item → CoefficientVector exponent degree) :
    fixedParityCompressed exponent degree parities bits highs =
      blockBinarySubsetSumAddHom bits highs +
        fixedParityCompressed exponent degree parities bits 0 := by
  funext block
  rw [Pi.add_apply]
  change coefficientHalf exponent degree
      (binarySubsetSum
        (joinCoefficientMasks exponent degree
          (fun item ↦ parities (block, item))
          (fun item ↦ highs (block, item)))
        (bits block)) = _
  rw [coefficientHalf_binarySubsetSum_joinCoefficientMasks
    exponent degree _ _ _ (hParity block)]
  simp only [fixedParityCompressed, blockBinarySubsetSumAddHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
  ac_rfl

/-- For fixed parity data with zero-sum block selectors, independently uniform high parts
compress to an exactly uniform lower-mask table. -/
theorem fixedParityCompressed_uniform_evalDist
    {Block Item : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Item] [DecidableEq Item]
    (exponent degree : ℕ)
    (parities : Block × Item → CoefficientVector 1 degree)
    (bits : Block → Item → Bool)
    (hParity : ∀ block,
      binarySubsetSum (fun item ↦ parities (block, item)) (bits block) = 0)
    (selected : Block → Item)
    (hselected : ∀ block, bits block (selected block) = true) :
    evalDist
        (fixedParityCompressed exponent degree parities bits <$>
          ($ᵗ (Block × Item → CoefficientVector exponent degree))) =
      evalDist ($ᵗ (Block → CoefficientVector exponent degree)) := by
  let transform := blockBinarySubsetSumAddHom
    (G := CoefficientVector exponent degree) bits
  let offset := fixedParityCompressed exponent degree parities bits 0
  have htransform : Function.Surjective transform :=
    blockBinarySubsetSumAddHom_surjective bits selected hselected
  have huniform :
      evalDist (transform <$>
          ($ᵗ (Block × Item → CoefficientVector exponent degree))) =
        evalDist ($ᵗ (Block → CoefficientVector exponent degree)) :=
    evalDist_map_surjective_addHom_uniform transform htransform
  have hfunction : fixedParityCompressed exponent degree parities bits =
      fun highs ↦ transform highs + offset := by
    funext highs
    exact fixedParityCompressed_eq_blockSum_add_offset
      exponent degree parities bits hParity highs
  rw [hfunction]
  calc
    evalDist ((fun highs ↦ transform highs + offset) <$>
        ($ᵗ (Block × Item → CoefficientVector exponent degree))) =
      evalDist ((fun output ↦ output + offset) <$>
        (transform <$>
          ($ᵗ (Block × Item → CoefficientVector exponent degree)))) := by
            simp only [Functor.map_map]
    _ = evalDist ((fun output ↦ output + offset) <$>
        ($ᵗ (Block → CoefficientVector exponent degree))) :=
      evalDist_map_eq_of_evalDist_eq huniform (fun output ↦ output + offset)
    _ = evalDist ($ᵗ (Block → CoefficientVector exponent degree)) :=
      evalDist_add_right_uniform
        (α := Block → CoefficientVector exponent degree) offset

/-- Exact two-adic layer for coefficient vectors. -/
def coefficientExactTwoLayer (exponent degree : ℕ) :
    ExactTwoLayer
      (CoefficientVector (exponent + 1) degree)
      (CoefficientVector exponent degree)
      (CoefficientVector 1 degree) where
  parity := coefficientParity exponent degree
  double := coefficientDouble exponent degree
  half := coefficientHalf exponent degree
  double_half_of_parity_zero value hParity := by
    funext coefficient
    apply scalarDouble_half_of_parity_zero
    exact congrFun hParity coefficient

/-! ## Binary linear algebra for one parity layer -/

/-- The canonical identification of a selector bit with its scalar in `ZMod 2`. -/
def boolEquivZModTwo : Bool ≃ ZMod 2 :=
  finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv

@[simp]
theorem boolEquivZModTwo_false : boolEquivZModTwo false = 0 := rfl

@[simp]
theorem boolEquivZModTwo_true : boolEquivZModTwo true = 1 := rfl

/-- Convert a field vector returned by binary linear algebra back into selector bits. -/
def fieldVectorToBits {count : ℕ} (values : Fin count → ZMod 2) :
    Fin count → Bool :=
  fun index ↦ boolEquivZModTwo.symm (values index)

@[simp]
theorem boolEquivZModTwo_fieldVectorToBits {count : ℕ}
    (values : Fin count → ZMod 2) (index : Fin count) :
    boolEquivZModTwo (fieldVectorToBits values index) = values index :=
  boolEquivZModTwo.apply_symm_apply _

/-- Put a family of parity masks into the usual row-by-column matrix orientation. -/
def parityMatrix {count degree : ℕ}
    (masks : Fin count → CoefficientVector 1 degree) :
    Matrix (Fin degree) (Fin count) (ZMod 2) :=
  fun coefficient index ↦ masks index coefficient

/-- A binary subset sum of parity masks is exactly matrix-vector multiplication over `ZMod 2`. -/
theorem binarySubsetSum_eq_parityMatrix_mulVec {count degree : ℕ}
    (masks : Fin count → CoefficientVector 1 degree)
    (bits : Fin count → Bool) :
    binarySubsetSum masks bits =
      (parityMatrix masks).mulVec (fun index ↦ boolEquivZModTwo (bits index)) := by
  classical
  funext coefficient
  simp only [binarySubsetSum, parityMatrix, Matrix.mulVec, dotProduct]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro index _
  cases bits index <;> simp

/-- Full row rank is precisely what is needed to solve every parity target. -/
theorem mulVec_surjective_of_rank_eq_height {F : Type} [Field F]
    (rows cols : ℕ) (matrix : Matrix (Fin rows) (Fin cols) F)
    (hfull : matrix.rank = rows) : Function.Surjective matrix.mulVec := by
  change Function.Surjective matrix.mulVecLin
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.range_mulVecLin, ← matrix.rank_eq_finrank_span_cols, hfull]
  simp

/-- A logical full-rank solver.  The later executable interface can replace this finite choice
without changing any lifting proof. -/
noncomputable def solveFullRowRank {rows cols : ℕ}
    (matrix : Matrix (Fin rows) (Fin cols) (ZMod 2))
    (hfull : matrix.rank = rows) (target : Fin rows → ZMod 2) :
    Fin cols → ZMod 2 :=
  Function.surjInv (mulVec_surjective_of_rank_eq_height rows cols matrix hfull) target

@[simp]
theorem solveFullRowRank_spec {rows cols : ℕ}
    (matrix : Matrix (Fin rows) (Fin cols) (ZMod 2))
    (hfull : matrix.rank = rows) (target : Fin rows → ZMod 2) :
    matrix.mulVec (solveFullRowRank matrix hfull target) = target :=
  Function.surjInv_eq (mulVec_surjective_of_rank_eq_height rows cols matrix hfull) target

/-- Selector bits obtained from a full-row-rank parity matrix. -/
noncomputable def fullRankSolutionBits {count degree : ℕ}
    (masks : Fin count → CoefficientVector 1 degree)
    (hfull : (parityMatrix masks).rank = degree)
    (target : CoefficientVector 1 degree) : Fin count → Bool :=
  fieldVectorToBits (solveFullRowRank (parityMatrix masks) hfull target)

/-- The full-rank selector exactly reaches its parity target. -/
theorem binarySubsetSum_fullRankSolutionBits {count degree : ℕ}
    (masks : Fin count → CoefficientVector 1 degree)
    (hfull : (parityMatrix masks).rank = degree)
    (target : CoefficientVector 1 degree) :
    binarySubsetSum masks (fullRankSolutionBits masks hfull target) = target := by
  rw [binarySubsetSum_eq_parityMatrix_mulVec]
  simp [fullRankSolutionBits]

/-- Every `N × (N+1)` binary matrix has a nonzero kernel vector. -/
theorem exists_nonzero_kernelVector (degree : ℕ)
    (matrix : Matrix (Fin degree) (Fin (degree + 1)) (ZMod 2)) :
    ∃ values : Fin (degree + 1) → ZMod 2,
      values ≠ 0 ∧ matrix.mulVec values = 0 := by
  have hker : LinearMap.ker matrix.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨values, hmem, hne⟩ := (Submodule.ne_bot_iff _).mp hker
  exact ⟨values, hne, LinearMap.mem_ker.mp hmem⟩

/-- A fixed nonzero parity-kernel vector, chosen for each block matrix. -/
noncomputable def nonzeroKernelVector (degree : ℕ)
    (matrix : Matrix (Fin degree) (Fin (degree + 1)) (ZMod 2)) :
    Fin (degree + 1) → ZMod 2 :=
  (exists_nonzero_kernelVector degree matrix).choose

theorem nonzeroKernelVector_ne_zero (degree : ℕ)
    (matrix : Matrix (Fin degree) (Fin (degree + 1)) (ZMod 2)) :
    nonzeroKernelVector degree matrix ≠ 0 :=
  (exists_nonzero_kernelVector degree matrix).choose_spec.1

@[simp]
theorem nonzeroKernelVector_spec (degree : ℕ)
    (matrix : Matrix (Fin degree) (Fin (degree + 1)) (ZMod 2)) :
    matrix.mulVec (nonzeroKernelVector degree matrix) = 0 :=
  (exists_nonzero_kernelVector degree matrix).choose_spec.2

/-- A nonempty binary subset whose parity sum is zero in an arbitrary block of `N+1` masks. -/
noncomputable def parityKernelBits (degree : ℕ)
    (masks : Fin (degree + 1) → CoefficientVector 1 degree) :
    Fin (degree + 1) → Bool :=
  fieldVectorToBits (nonzeroKernelVector degree (parityMatrix masks))

theorem parityKernelBits_ne_zero (degree : ℕ)
    (masks : Fin (degree + 1) → CoefficientVector 1 degree) :
    parityKernelBits degree masks ≠ fun _ ↦ false := by
  intro hzero
  apply nonzeroKernelVector_ne_zero degree (parityMatrix masks)
  funext index
  have := congrFun hzero index
  have hfield := congrArg boolEquivZModTwo this
  simpa [parityKernelBits] using hfield

@[simp]
theorem binarySubsetSum_parityKernelBits (degree : ℕ)
    (masks : Fin (degree + 1) → CoefficientVector 1 degree) :
    binarySubsetSum masks (parityKernelBits degree masks) = 0 := by
  rw [binarySubsetSum_eq_parityMatrix_mulVec]
  simp [parityKernelBits]

/-- Apply the canonical parity-kernel choice to every disjoint block. -/
noncomputable def blockParityKernelBits {Block : Type} (degree : ℕ)
    (parities : Block × Fin (degree + 1) → CoefficientVector 1 degree) :
    Block → Fin (degree + 1) → Bool :=
  fun block ↦ parityKernelBits degree (fun item ↦ parities (block, item))

theorem blockParityKernelBits_paritySum (degree : ℕ)
    {Block : Type}
    (parities : Block × Fin (degree + 1) → CoefficientVector 1 degree)
    (block : Block) :
    binarySubsetSum (fun item ↦ parities (block, item))
      (blockParityKernelBits degree parities block) = 0 :=
  binarySubsetSum_parityKernelBits degree (fun item ↦ parities (block, item))

/-- A selected pivot in each canonical nonempty kernel subset. -/
noncomputable def blockParityKernelSelected {Block : Type} (degree : ℕ)
    (parities : Block × Fin (degree + 1) → CoefficientVector 1 degree) :
    Block → Fin (degree + 1) :=
  fun block ↦ selectedTrue (blockParityKernelBits degree parities block)
    (parityKernelBits_ne_zero degree (fun item ↦ parities (block, item)))

theorem blockParityKernelSelected_spec (degree : ℕ)
    {Block : Type}
    (parities : Block × Fin (degree + 1) → CoefficientVector 1 degree)
    (block : Block) :
    blockParityKernelBits degree parities block
      (blockParityKernelSelected degree parities block) = true :=
  selectedTrue_spec _ _

/-- Split a table of upper residues, choose one nonempty zero-parity subset in every block, and
compress the chosen block sums to the next lower modulus. -/
noncomputable def parityKernelCompressedUpper {Block : Type}
    (exponent degree : ℕ)
    (upper : Block × Fin (degree + 1) →
      CoefficientVector (exponent + 1) degree) :
    Block → CoefficientVector exponent degree :=
  let split := coefficientTableSplitEquiv
    (Block × Fin (degree + 1)) exponent degree upper
  fixedParityCompressed exponent degree split.1
    (blockParityKernelBits degree split.1) split.2

/-- The parity-kernel compression of a uniformly sampled upper table is an exactly uniform lower
table.  This is the distribution-preservation step needed by the recursive rank argument. -/
theorem parityKernelCompressedUpper_uniform_evalDist
    {Block : Type} [Fintype Block] [DecidableEq Block]
    (exponent degree : ℕ) :
    evalDist
        (parityKernelCompressedUpper (Block := Block) exponent degree <$>
          ($ᵗ (Block × Fin (degree + 1) →
            CoefficientVector (exponent + 1) degree))) =
      evalDist ($ᵗ (Block → CoefficientVector exponent degree)) := by
  let ParityTable :=
    Block × Fin (degree + 1) → CoefficientVector 1 degree
  let HighTable :=
    Block × Fin (degree + 1) → CoefficientVector exponent degree
  let UpperTable :=
    Block × Fin (degree + 1) → CoefficientVector (exponent + 1) degree
  let OutputTable := Block → CoefficientVector exponent degree
  let splitEquiv := coefficientTableSplitEquiv
    (Block × Fin (degree + 1)) exponent degree
  let finish : ParityTable × HighTable → OutputTable := fun split ↦
    fixedParityCompressed exponent degree split.1
      (blockParityKernelBits degree split.1) split.2
  have hsplit :
      evalDist (splitEquiv <$> ($ᵗ UpperTable)) =
        evalDist ($ᵗ (ParityTable × HighTable)) :=
    evalDist_map_bijective_uniform_cross
      (α := UpperTable) (β := ParityTable × HighTable)
      splitEquiv splitEquiv.bijective
  have hproduct :
      evalDist (do
        let parities ← $ᵗ ParityTable
        let highs ← $ᵗ HighTable
        return (parities, highs)) =
        evalDist ($ᵗ (ParityTable × HighTable)) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have hconditional (parities : ParityTable) :
      evalDist
          (fixedParityCompressed exponent degree parities
              (blockParityKernelBits degree parities) <$> ($ᵗ HighTable)) =
        evalDist ($ᵗ OutputTable) :=
    fixedParityCompressed_uniform_evalDist exponent degree parities
      (blockParityKernelBits degree parities)
      (blockParityKernelBits_paritySum degree parities)
      (blockParityKernelSelected degree parities)
      (blockParityKernelSelected_spec degree parities)
  calc
    evalDist
        (parityKernelCompressedUpper (Block := Block) exponent degree <$>
          ($ᵗ UpperTable)) =
      evalDist (finish <$> (splitEquiv <$> ($ᵗ UpperTable))) := by
        simp only [Functor.map_map]
        congr 2
    _ = evalDist (finish <$> ($ᵗ (ParityTable × HighTable))) :=
      evalDist_map_eq_of_evalDist_eq hsplit finish
    _ = evalDist (finish <$> (do
        let parities ← $ᵗ ParityTable
        let highs ← $ᵗ HighTable
        return (parities, highs))) :=
      evalDist_map_eq_of_evalDist_eq hproduct.symm finish
    _ = evalDist (do
        let parities ← $ᵗ ParityTable
        fixedParityCompressed exponent degree parities
          (blockParityKernelBits degree parities) <$> ($ᵗ HighTable)) := by
      congr 1
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
      rfl
    _ = evalDist (do
        let _parities ← $ᵗ ParityTable
        ($ᵗ OutputTable)) := by
      apply evalDist_bind_congr' ($ᵗ ParityTable)
      exact hconditional
    _ = evalDist ($ᵗ OutputTable) := by
      apply evalDist_ext
      intro output
      rw [probOutput_bind_const]
      simp

/-- Direct pointwise form of parity-kernel compression, after recombining the split low/high
representation back to the original upper masks. -/
theorem parityKernelCompressedUpper_apply
    {Block : Type} (exponent degree : ℕ)
    (upper : Block × Fin (degree + 1) →
      CoefficientVector (exponent + 1) degree)
    (block : Block) :
    parityKernelCompressedUpper exponent degree upper block =
      coefficientHalf exponent degree
        (binarySubsetSum (fun item ↦ upper (block, item))
          (parityKernelBits degree
            (fun item ↦ coefficientParity exponent degree (upper (block, item))))) := by
  classical
  unfold parityKernelCompressedUpper fixedParityCompressed blockParityKernelBits
  congr 2
  · funext item
    exact (coefficientSplitEquiv exponent degree).symm_apply_apply (upper (block, item))

/-! ## A proved one-layer selector -/

/-- Solve the prefix parity equation for one two-adic lifting layer. -/
noncomputable def liftingPrefixBits (exponent degree slack lowerCount : ℕ)
    (masks : LayerIndex (degree + slack) (degree + 1) lowerCount →
      CoefficientVector (exponent + 1) degree)
    (target : CoefficientVector (exponent + 1) degree)
    (hfull :
      (parityMatrix
        ((coefficientParity exponent degree) ∘ prefixMasks masks)).rank = degree) :
    Fin (degree + slack) → Bool :=
  fullRankSolutionBits
    ((coefficientParity exponent degree) ∘ prefixMasks masks)
    hfull
    (coefficientParity exponent degree target)

/-- Choose a nonempty parity-zero subset independently inside each disjoint block. -/
noncomputable def liftingKernelBits (exponent degree slack lowerCount : ℕ)
    (masks : LayerIndex (degree + slack) (degree + 1) lowerCount →
      CoefficientVector (exponent + 1) degree) :
    Fin lowerCount → Fin (degree + 1) → Bool :=
  fun lowerIndex ↦ parityKernelBits degree
    ((coefficientParity exponent degree) ∘ blockMasks masks lowerIndex)

/-- Every block subset used for compression is genuinely nonempty. -/
theorem liftingKernelBits_ne_zero (exponent degree slack lowerCount : ℕ)
    (masks : LayerIndex (degree + slack) (degree + 1) lowerCount →
      CoefficientVector (exponent + 1) degree)
    (lowerIndex : Fin lowerCount) :
    liftingKernelBits exponent degree slack lowerCount masks lowerIndex ≠
      fun _ ↦ false :=
  parityKernelBits_ne_zero degree
    ((coefficientParity exponent degree) ∘ blockMasks masks lowerIndex)

/-- If the prefix parity matrix has full row rank and the recursively compressed instance has a
solution, the explicitly assembled upper-layer bit vector is an exact subset-sum preimage. -/
theorem binarySubsetSum_lift_of_fullRank_and_lowerSolution
    (exponent degree slack lowerCount : ℕ)
    (masks : LayerIndex (degree + slack) (degree + 1) lowerCount →
      CoefficientVector (exponent + 1) degree)
    (target : CoefficientVector (exponent + 1) degree)
    (hfull :
      (parityMatrix
        ((coefficientParity exponent degree) ∘ prefixMasks masks)).rank = degree)
    (lowerBits : Fin lowerCount → Bool)
    (hLower :
      binarySubsetSum
          (compressedMasks (coefficientExactTwoLayer exponent degree) masks
            (liftingKernelBits exponent degree slack lowerCount masks))
          lowerBits =
        coefficientHalf exponent degree
          (target - binarySubsetSum (prefixMasks masks)
            (liftingPrefixBits exponent degree slack lowerCount masks target hfull))) :
    binarySubsetSum masks
        (liftBits
          (liftingPrefixBits exponent degree slack lowerCount masks target hfull)
          (liftingKernelBits exponent degree slack lowerCount masks)
          lowerBits) = target := by
  apply binarySubsetSum_liftBits_eq_target
    (coefficientExactTwoLayer exponent degree) masks target
  · exact binarySubsetSum_fullRankSolutionBits
      ((coefficientParity exponent degree) ∘ prefixMasks masks)
      hfull
      (coefficientParity exponent degree target)
  · intro lowerIndex
    exact binarySubsetSum_parityKernelBits degree
      ((coefficientParity exponent degree) ∘ blockMasks masks lowerIndex)
  · exact hLower

/-! ## Rank-failure probability of the prefix -/

theorem rank_parityMatrix {count degree : ℕ}
    (masks : Fin count → CoefficientVector 1 degree) :
    (parityMatrix masks).rank = (show Matrix (Fin count) (Fin degree) (ZMod 2) from masks).rank := by
  change (Matrix.transpose
    (show Matrix (Fin count) (Fin degree) (ZMod 2) from masks)).rank = _
  exact Matrix.rank_transpose _

/-- A uniform family of `degree + slack` parity masks fails to span the target space with the
standard rectangular-matrix probability.  Over `ZMod 2` this is at most `2 / 2^(slack+1)`. -/
theorem parityMatrix_rankFailure_le (degree slack : ℕ) :
    Pr[(fun masks : Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2) ↦
      (parityMatrix masks).rank < degree) |
      ($ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2))] ≤
      2 / (2 : ℝ≥0∞) ^ (slack + 1) := by
  calc
    Pr[(fun masks : Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2) ↦
        (parityMatrix masks).rank < degree) |
        ($ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2))] =
      Pr[(fun matrix : Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2) ↦
        matrix.rank < degree) |
        ($ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2))] := by
          apply probEvent_congr' (fun masks _ ↦ ?_) rfl
          rw [rank_parityMatrix]
    _ ≤ 2 / (Fintype.card (ZMod 2) : ℝ≥0∞) ^ (slack + 1) :=
      FormalProof4FHE.FiniteFieldRank.rankFailure_le
        (F := ZMod 2) degree slack
    _ = 2 / (2 : ℝ≥0∞) ^ (slack + 1) := by norm_num

/-- The same rank bound for the coefficient-table sampler used by the lifting recursion. -/
theorem parityTable_rankFailure_le (degree slack : ℕ) :
    Pr[(fun masks : Fin (degree + slack) → CoefficientVector 1 degree ↦
      (parityMatrix masks).rank < degree) |
      ($ᵗ (Fin (degree + slack) → CoefficientVector 1 degree))] ≤
      2 / (2 : ℝ≥0∞) ^ (slack + 1) := by
  have hdist :
      evalDist ($ᵗ (Fin (degree + slack) → CoefficientVector 1 degree)) =
        evalDist ($ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2)) := by
    apply evalDist_ext
    intro masks
    change
      Pr[= masks |
          $ᵗ (Fin (degree + slack) → CoefficientVector 1 degree)] =
        Pr[= (show Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2) from masks) |
          $ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2)]
    calc
      Pr[= masks |
          $ᵗ (Fin (degree + slack) → CoefficientVector 1 degree)] =
        (Fintype.card
          (Fin (degree + slack) → CoefficientVector 1 degree) : ℝ≥0∞)⁻¹ :=
        probOutput_uniformSample _ masks
      _ = Pr[= (show Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2) from masks) |
          $ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2)] :=
        (probOutput_uniformSample
          (Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2)) masks).symm
  calc
    Pr[(fun masks : Fin (degree + slack) → CoefficientVector 1 degree ↦
        (parityMatrix masks).rank < degree) |
        ($ᵗ (Fin (degree + slack) → CoefficientVector 1 degree))] =
      Pr[(fun masks : Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2) ↦
        (parityMatrix masks).rank < degree) |
        ($ᵗ Matrix (Fin (degree + slack)) (Fin degree) (ZMod 2))] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) hdist
    _ ≤ 2 / (2 : ℝ≥0∞) ^ (slack + 1) :=
      parityMatrix_rankFailure_le degree slack

/-! ## Recursive exact selector -/

/-- Flatten the prefix-plus-block layout into the source-count index. -/
def layerIndexEquiv (prefixCount blockCount lowerCount : ℕ) :
    LayerIndex prefixCount blockCount lowerCount ≃
      Fin (prefixCount + blockCount * lowerCount) :=
  (Equiv.sumCongr (Equiv.refl (Fin prefixCount))
      ((Equiv.prodComm (Fin lowerCount) (Fin blockCount)).trans finProdFinEquiv)).trans
    finSumFinEquiv

/-- The source-count recurrence has exactly the layout consumed by one lifting layer. -/
def sourceLayerEquiv (depth degree slack : ℕ) :
    LayerIndex (degree + slack) (degree + 1) (sourceCount depth degree slack) ≃
      Fin (sourceCount (depth + 1) degree slack) := by
  rw [sourceCount_succ]
  exact layerIndexEquiv (degree + slack) (degree + 1)
    (sourceCount depth degree slack)

/-- Binary subset sums are invariant under a bijective reindexing of their source masks. -/
theorem binarySubsetSum_reindex
    {First Second G : Type} [Fintype First] [Fintype Second]
    [DecidableEq First] [DecidableEq Second] [AddCommMonoid G]
    (equivalence : First ≃ Second) (table : Second → G) (bits : Second → Bool) :
    binarySubsetSum table bits =
      binarySubsetSum (table ∘ equivalence) (bits ∘ equivalence) := by
  unfold binarySubsetSum
  apply Fintype.sum_equiv equivalence.symm
  intro index
  simp

/-- View a flat successor source table as one prefix followed by disjoint lifting blocks. -/
def asLayerMasks (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    LayerIndex (degree + slack) (degree + 1) (sourceCount depth degree slack) →
      CoefficientVector (depth + 2) degree :=
  masks ∘ sourceLayerEquiv depth degree slack

/-- Embed the fresh parity-solving prefix into a flat successor source table. -/
def successorPrefixEmbedding (depth degree slack : ℕ) :
    Fin (degree + slack) → Fin (sourceCount (depth + 1) degree slack) :=
  fun index ↦ sourceLayerEquiv depth degree slack (Sum.inl index)

theorem successorPrefixEmbedding_injective (depth degree slack : ℕ) :
    Function.Injective (successorPrefixEmbedding depth degree slack) :=
  (sourceLayerEquiv depth degree slack).injective.comp Sum.inl_injective

/-- The upper residues in the fresh prefix. -/
def successorPrefixUpperTable (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    Fin (degree + slack) → CoefficientVector (depth + 2) degree :=
  masks ∘ successorPrefixEmbedding depth degree slack

/-- The low-bit table whose full rank is tested at a successor layer. -/
def successorPrefixParityTable (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    Fin (degree + slack) → CoefficientVector 1 degree :=
  (coefficientParity (depth + 1) degree) ∘
    successorPrefixUpperTable depth degree slack masks

theorem successorPrefixParityTable_eq_layerPrefix
    (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    successorPrefixParityTable depth degree slack masks =
      (coefficientParity (depth + 1) degree) ∘
        prefixMasks (asLayerMasks depth degree slack masks) := rfl

/-- A fresh prefix extracted from uniform successor masks has an exactly uniform parity table. -/
theorem successorPrefixParityTable_uniform_evalDist
    (depth degree slack : ℕ) :
    evalDist
        (successorPrefixParityTable depth degree slack <$>
          ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
            CoefficientVector (depth + 2) degree))) =
      evalDist
        ($ᵗ (Fin (degree + slack) → CoefficientVector 1 degree)) := by
  let Prefix := Fin (degree + slack)
  let FlatIndex := Fin (sourceCount (depth + 1) degree slack)
  let embedding : Prefix → FlatIndex :=
    successorPrefixEmbedding depth degree slack
  have hembedding : Function.Injective embedding :=
    successorPrefixEmbedding_injective depth degree slack
  have hrestrict :
      evalDist
          (successorPrefixUpperTable depth degree slack <$>
            ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree))) =
        evalDist
          ($ᵗ (Prefix → CoefficientVector (depth + 2) degree)) := by
    change evalDist
        ((fun masks : FlatIndex → CoefficientVector (depth + 2) degree ↦
            masks ∘ embedding) <$>
          ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree))) = _
    simpa only [bind_pure_comp] using
      (evalDist_uniformSample_map_comp_injective
        (A := Prefix) (B := FlatIndex)
        (R := CoefficientVector (depth + 2) degree) hembedding)
  have hparity :
      evalDist
          (coefficientParityTableAddHom Prefix (depth + 1) degree <$>
            ($ᵗ (Prefix → CoefficientVector (depth + 2) degree))) =
        evalDist ($ᵗ (Prefix → CoefficientVector 1 degree)) := by
    apply evalDist_map_surjective_addHom_uniform
    exact coefficientParityTableAddHom_surjective Prefix (depth + 1) degree
  calc
    evalDist
        (successorPrefixParityTable depth degree slack <$>
          ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree))) =
      evalDist
        (coefficientParityTableAddHom Prefix (depth + 1) degree <$>
          (successorPrefixUpperTable depth degree slack <$>
            ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree)))) := by
        simp only [Functor.map_map]
        rfl
    _ = evalDist
        (coefficientParityTableAddHom Prefix (depth + 1) degree <$>
          ($ᵗ (Prefix → CoefficientVector (depth + 2) degree))) :=
      evalDist_map_eq_of_evalDist_eq hrestrict
        (coefficientParityTableAddHom Prefix (depth + 1) degree)
    _ = evalDist ($ᵗ (Prefix → CoefficientVector 1 degree)) := hparity

/-- The fresh prefix rank failure at every successor layer has the same binary rectangular-matrix
bound as the base layer. -/
theorem successorPrefixRankFailure_le (depth degree slack : ℕ) :
    Pr[(fun masks : Fin (sourceCount (depth + 1) degree slack) →
        CoefficientVector (depth + 2) degree ↦
      (parityMatrix (successorPrefixParityTable depth degree slack masks)).rank < degree) |
      ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
        CoefficientVector (depth + 2) degree))] ≤
      2 / (2 : ℝ≥0∞) ^ (slack + 1) := by
  have hdist := successorPrefixParityTable_uniform_evalDist depth degree slack
  calc
    Pr[(fun masks : Fin (sourceCount (depth + 1) degree slack) →
          CoefficientVector (depth + 2) degree ↦
        (parityMatrix (successorPrefixParityTable depth degree slack masks)).rank < degree) |
        ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
          CoefficientVector (depth + 2) degree))] =
      Pr[(fun table : Fin (degree + slack) → CoefficientVector 1 degree ↦
          (parityMatrix table).rank < degree) |
        successorPrefixParityTable depth degree slack <$>
          ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
            CoefficientVector (depth + 2) degree))] :=
      by
        change
          Pr[((fun table : Fin (degree + slack) → CoefficientVector 1 degree ↦
              (parityMatrix table).rank < degree) ∘
                successorPrefixParityTable depth degree slack) |
            ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
              CoefficientVector (depth + 2) degree))] = _
        exact (probEvent_map
          ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
            CoefficientVector (depth + 2) degree))
          (successorPrefixParityTable depth degree slack)
          (fun table : Fin (degree + slack) → CoefficientVector 1 degree ↦
            (parityMatrix table).rank < degree)).symm
    _ = Pr[(fun table : Fin (degree + slack) → CoefficientVector 1 degree ↦
          (parityMatrix table).rank < degree) |
        ($ᵗ (Fin (degree + slack) → CoefficientVector 1 degree))] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) hdist
    _ ≤ 2 / (2 : ℝ≥0∞) ^ (slack + 1) :=
      parityTable_rankFailure_le degree slack

/-- Embed the block portion of a successor layout into the flat source table. -/
def successorBlockEmbedding (depth degree slack : ℕ) :
    Fin (sourceCount depth degree slack) × Fin (degree + 1) →
      Fin (sourceCount (depth + 1) degree slack) :=
  fun pair ↦ sourceLayerEquiv depth degree slack (Sum.inr pair)

theorem successorBlockEmbedding_injective (depth degree slack : ℕ) :
    Function.Injective (successorBlockEmbedding depth degree slack) :=
  (sourceLayerEquiv depth degree slack).injective.comp Sum.inr_injective

/-- Restrict a flat successor table to the disjoint block masks used for recursion. -/
def successorBlockTable (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    Fin (sourceCount depth degree slack) × Fin (degree + 1) →
      CoefficientVector (depth + 2) degree :=
  masks ∘ successorBlockEmbedding depth degree slack

/-- The lower-modulus mask table produced by the disjoint nonempty block kernels. -/
noncomputable def recursiveCompressedMasks (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    Fin (sourceCount depth degree slack) → CoefficientVector (depth + 1) degree :=
  let layerMasks := asLayerMasks depth degree slack masks
  compressedMasks (coefficientExactTwoLayer (depth + 1) degree) layerMasks
    (liftingKernelBits (depth + 1) degree slack
      (sourceCount depth degree slack) layerMasks)

/-- The recursive compression is exactly the parity-kernel compression of the block restriction. -/
theorem recursiveCompressedMasks_eq_parityKernelCompressedUpper
    (depth degree slack : ℕ)
    (masks : Fin (sourceCount (depth + 1) degree slack) →
      CoefficientVector (depth + 2) degree) :
    recursiveCompressedMasks depth degree slack masks =
      parityKernelCompressedUpper (Block := Fin (sourceCount depth degree slack))
        (depth + 1) degree (successorBlockTable depth degree slack masks) := by
  funext lowerIndex
  rw [parityKernelCompressedUpper_apply]
  rfl

set_option maxHeartbeats 2000000

/-- Consequently, uniform successor masks induce an exactly uniform recursive lower table. -/
theorem recursiveCompressedMasks_uniform_evalDist (depth degree slack : ℕ) :
    evalDist
        (recursiveCompressedMasks depth degree slack <$>
          ($ᵗ (Fin (sourceCount (depth + 1) degree slack) →
            CoefficientVector (depth + 2) degree))) =
      evalDist
        ($ᵗ (Fin (sourceCount depth degree slack) →
          CoefficientVector (depth + 1) degree)) := by
  let Block := Fin (sourceCount depth degree slack)
  let FlatIndex := Fin (sourceCount (depth + 1) degree slack)
  let embedding : Block × Fin (degree + 1) → FlatIndex :=
    successorBlockEmbedding depth degree slack
  have hembedding : Function.Injective embedding :=
    successorBlockEmbedding_injective depth degree slack
  have hrestrict :
      evalDist
          (successorBlockTable depth degree slack <$>
            ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree))) =
        evalDist
          ($ᵗ (Block × Fin (degree + 1) →
            CoefficientVector (depth + 2) degree)) := by
    change evalDist
        ((fun masks : FlatIndex → CoefficientVector (depth + 2) degree ↦
            masks ∘ embedding) <$>
          ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree))) = _
    simpa only [bind_pure_comp] using
      (evalDist_uniformSample_map_comp_injective
        (A := Block × Fin (degree + 1)) (B := FlatIndex)
        (R := CoefficientVector (depth + 2) degree) hembedding)
  let canonicalUpper : ProbComp
      (Block × Fin (degree + 1) →
        CoefficientVector (depth + 1 + 1) degree) :=
    @uniformSample
      (Block × Fin (degree + 1) →
        CoefficientVector (depth + 1 + 1) degree)
      instSampleableTypePiFintype
  have hsourceUniform :
      evalDist
          ($ᵗ (Block × Fin (degree + 1) →
            CoefficientVector (depth + 2) degree)) =
        evalDist canonicalUpper := by
    apply evalDist_ext
    intro table
    simp only [canonicalUpper, probOutput_uniformSample]
  calc
    evalDist
        (recursiveCompressedMasks depth degree slack <$>
          ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree))) =
      evalDist
        (parityKernelCompressedUpper (Block := Block) (depth + 1) degree <$>
          (successorBlockTable depth degree slack <$>
            ($ᵗ (FlatIndex → CoefficientVector (depth + 2) degree)))) := by
        simp only [Functor.map_map]
        congr 2
        funext masks
        exact recursiveCompressedMasks_eq_parityKernelCompressedUpper
          depth degree slack masks
    _ = evalDist
        (parityKernelCompressedUpper (Block := Block) (depth + 1) degree <$>
          ($ᵗ (Block × Fin (degree + 1) →
            CoefficientVector (depth + 2) degree))) :=
      evalDist_map_eq_of_evalDist_eq hrestrict
        (parityKernelCompressedUpper (Block := Block) (depth + 1) degree)
    _ = evalDist
        (parityKernelCompressedUpper (Block := Block) (depth + 1) degree <$>
          canonicalUpper) :=
      evalDist_map_eq_of_evalDist_eq hsourceUniform
        (parityKernelCompressedUpper (Block := Block) (depth + 1) degree)
    _ = evalDist
        ($ᵗ (Block → CoefficientVector (depth + 1) degree)) :=
      by
        simpa [canonicalUpper] using
          (parityKernelCompressedUpper_uniform_evalDist
            (Block := Block) (depth + 1) degree)

set_option maxHeartbeats 200000

/-- Rank conditions encountered by the recursive selector.  At depth zero this is the single
binary spanning condition.  At a successor it is the fresh prefix condition plus the condition
recursively induced on the compressed masks. -/
def LiftingGood (degree slack : ℕ) :
    (depth : ℕ) →
      (Fin (sourceCount depth degree slack) →
        CoefficientVector (depth + 1) degree) → Prop
  | 0, masks => (parityMatrix masks).rank = degree
  | depth + 1, masks =>
      let layerMasks := asLayerMasks depth degree slack masks
      (parityMatrix
          ((coefficientParity (depth + 1) degree) ∘ prefixMasks layerMasks)).rank = degree ∧
        LiftingGood degree slack depth
          (recursiveCompressedMasks depth degree slack masks)

/-- The complete recursive rank condition fails with probability at most one binary rank-failure
term per two-adic layer. -/
theorem liftingGood_failure_le (degree slack : ℕ) :
    ∀ depth : ℕ,
      Pr[(fun masks : Fin (sourceCount depth degree slack) →
          CoefficientVector (depth + 1) degree ↦
        ¬ LiftingGood degree slack depth masks) |
        ($ᵗ (Fin (sourceCount depth degree slack) →
          CoefficientVector (depth + 1) degree))] ≤
        (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
  intro depth
  induction depth with
  | zero =>
      calc
        Pr[(fun masks : Fin (sourceCount 0 degree slack) →
              CoefficientVector 1 degree ↦
            ¬ LiftingGood degree slack 0 masks) |
            ($ᵗ (Fin (sourceCount 0 degree slack) →
              CoefficientVector 1 degree))] =
          Pr[(fun masks : Fin (degree + slack) → CoefficientVector 1 degree ↦
              (parityMatrix masks).rank < degree) |
            ($ᵗ (Fin (degree + slack) → CoefficientVector 1 degree))] := by
              apply probEvent_congr' (fun masks _ ↦ ?_) rfl
              change ¬ (parityMatrix masks).rank = degree ↔
                (parityMatrix masks).rank < degree
              have hle := Matrix.rank_le_height (parityMatrix masks)
              omega
        _ ≤ 2 / (2 : ℝ≥0∞) ^ (slack + 1) :=
          parityTable_rankFailure_le degree slack
        _ = (0 + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by simp
  | succ depth inductionHypothesis =>
      let UpperMasks := Fin (sourceCount (depth + 1) degree slack) →
        CoefficientVector (depth + 2) degree
      let upperSampler : ProbComp UpperMasks := $ᵗ UpperMasks
      let prefixGood : UpperMasks → Prop := fun masks ↦
        (parityMatrix (successorPrefixParityTable depth degree slack masks)).rank = degree
      let lowerGood : UpperMasks → Prop := fun masks ↦
        LiftingGood degree slack depth
          (recursiveCompressedMasks depth degree slack masks)
      have hfailure (masks : UpperMasks) :
          (¬ LiftingGood degree slack (depth + 1) masks) ↔
            (¬ prefixGood masks ∨ ¬ lowerGood masks) := by
        simp only [LiftingGood, prefixGood, lowerGood, not_and_or]
        rw [successorPrefixParityTable_eq_layerPrefix]
      have hprefix :
          Pr[(fun masks ↦ ¬ prefixGood masks) | upperSampler] ≤
            2 / (2 : ℝ≥0∞) ^ (slack + 1) := by
        calc
          Pr[(fun masks ↦ ¬ prefixGood masks) | upperSampler] =
            Pr[(fun masks : UpperMasks ↦
                (parityMatrix
                  (successorPrefixParityTable depth degree slack masks)).rank < degree) |
              upperSampler] := by
                apply probEvent_congr' (fun masks _ ↦ ?_) rfl
                dsimp [prefixGood]
                have hle := Matrix.rank_le_height
                  (parityMatrix (successorPrefixParityTable depth degree slack masks))
                omega
          _ ≤ 2 / (2 : ℝ≥0∞) ^ (slack + 1) :=
            successorPrefixRankFailure_le depth degree slack
      have hlower :
          Pr[(fun masks ↦ ¬ lowerGood masks) | upperSampler] ≤
            (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
        let lowerFailure := fun masks :
            Fin (sourceCount depth degree slack) →
              CoefficientVector (depth + 1) degree ↦
          ¬ LiftingGood degree slack depth masks
        have hmap :
            Pr[(fun masks ↦ ¬ lowerGood masks) | upperSampler] =
              Pr[lowerFailure |
                recursiveCompressedMasks depth degree slack <$> upperSampler] := by
          change Pr[(lowerFailure ∘ recursiveCompressedMasks depth degree slack) |
              upperSampler] = _
          exact (probEvent_map upperSampler
            (recursiveCompressedMasks depth degree slack) lowerFailure).symm
        rw [hmap]
        calc
          Pr[lowerFailure |
              recursiveCompressedMasks depth degree slack <$> upperSampler] =
            Pr[lowerFailure |
              ($ᵗ (Fin (sourceCount depth degree slack) →
                CoefficientVector (depth + 1) degree))] :=
            probEvent_congr' (fun _ _ ↦ Iff.rfl)
              (recursiveCompressedMasks_uniform_evalDist depth degree slack)
          _ ≤ (depth + 1 : ℕ) *
              (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := inductionHypothesis
      calc
        Pr[(fun masks : UpperMasks ↦
              ¬ LiftingGood degree slack (depth + 1) masks) |
            upperSampler] =
          Pr[(fun masks ↦ ¬ prefixGood masks ∨ ¬ lowerGood masks) |
            upperSampler] :=
          probEvent_congr' (fun masks _ ↦ hfailure masks) rfl
        _ ≤ Pr[(fun masks ↦ ¬ prefixGood masks) | upperSampler] +
            Pr[(fun masks ↦ ¬ lowerGood masks) | upperSampler] :=
          probEvent_or_le upperSampler _ _
        _ ≤ 2 / (2 : ℝ≥0∞) ^ (slack + 1) +
            (depth + 1 : ℕ) *
              (2 / (2 : ℝ≥0∞) ^ (slack + 1)) :=
          add_le_add hprefix hlower
        _ = (depth + 1 + 1 : ℕ) *
            (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
          push_cast
          ring

/-- Under the recursively exposed rank conditions, the power-of-two lifting construction gives
an exact binary preimage for every target. -/
theorem exists_binarySubsetSum_eq_of_liftingGood (degree slack : ℕ) :
    ∀ (depth : ℕ)
      (masks : Fin (sourceCount depth degree slack) →
        CoefficientVector (depth + 1) degree)
      (target : CoefficientVector (depth + 1) degree),
      LiftingGood degree slack depth masks →
        ∃ bits : Fin (sourceCount depth degree slack) → Bool,
          binarySubsetSum masks bits = target := by
  intro depth
  induction depth with
  | zero =>
      intro masks target hgood
      refine ⟨fullRankSolutionBits masks hgood target, ?_⟩
      exact binarySubsetSum_fullRankSolutionBits masks hgood target
  | succ depth inductionHypothesis =>
      intro masks target hgood
      let layerMasks := asLayerMasks depth degree slack masks
      let kernelBits := liftingKernelBits (depth + 1) degree slack
        (sourceCount depth degree slack) layerMasks
      let prefixBits := liftingPrefixBits (depth + 1) degree slack
        (sourceCount depth degree slack) layerMasks target hgood.1
      let lowerMasks := recursiveCompressedMasks depth degree slack masks
      let lowerTarget := coefficientHalf (depth + 1) degree
        (target - binarySubsetSum (prefixMasks layerMasks) prefixBits)
      obtain ⟨lowerBits, hLower⟩ :=
        inductionHypothesis lowerMasks lowerTarget hgood.2
      let liftedBits := liftBits prefixBits kernelBits lowerBits
      refine ⟨liftedBits ∘ (sourceLayerEquiv depth degree slack).symm, ?_⟩
      rw [binarySubsetSum_reindex
        (sourceLayerEquiv depth degree slack) masks
        (liftedBits ∘ (sourceLayerEquiv depth degree slack).symm)]
      have htable : masks ∘ sourceLayerEquiv depth degree slack = layerMasks := rfl
      have hbits :
          (liftedBits ∘ (sourceLayerEquiv depth degree slack).symm) ∘
              sourceLayerEquiv depth degree slack = liftedBits := by
        funext index
        simp
      rw [htable, hbits]
      apply binarySubsetSum_lift_of_fullRank_and_lowerSolution
        (depth + 1) degree slack (sourceCount depth degree slack)
        layerMasks target hgood.1 lowerBits
      simpa [lowerMasks, lowerTarget, prefixBits, kernelBits,
        recursiveCompressedMasks, layerMasks] using hLower

/-- A canonical logical selector extracted from the proved recursive existence theorem.  A later
implementation may replace this choice by Gaussian elimination without changing its contract. -/
noncomputable def recursiveSelector (depth degree slack : ℕ)
    (masks : Fin (sourceCount depth degree slack) →
      CoefficientVector (depth + 1) degree)
    (target : CoefficientVector (depth + 1) degree)
    (hgood : LiftingGood degree slack depth masks) :
    Fin (sourceCount depth degree slack) → Bool :=
  (exists_binarySubsetSum_eq_of_liftingGood degree slack depth masks target hgood).choose

@[simp]
theorem recursiveSelector_spec (depth degree slack : ℕ)
    (masks : Fin (sourceCount depth degree slack) →
      CoefficientVector (depth + 1) degree)
    (target : CoefficientVector (depth + 1) degree)
    (hgood : LiftingGood degree slack depth masks) :
    binarySubsetSum masks
      (recursiveSelector depth degree slack masks target hgood) = target :=
  (exists_binarySubsetSum_eq_of_liftingGood degree slack depth masks target hgood).choose_spec

/-- Total selector: use the proved recursive selector on good rank instances and return zero bits
on the exceptional instances. -/
noncomputable def powerOfTwoSelector (depth degree slack : ℕ)
    (masks : Fin (sourceCount depth degree slack) →
      CoefficientVector (depth + 1) degree)
    (target : CoefficientVector (depth + 1) degree) :
    Fin (sourceCount depth degree slack) → Bool := by
  classical
  exact if hgood : LiftingGood degree slack depth masks then
      recursiveSelector depth degree slack masks target hgood
    else
      fun _ ↦ false

theorem powerOfTwoSelector_spec_of_good (depth degree slack : ℕ)
    (masks : Fin (sourceCount depth degree slack) →
      CoefficientVector (depth + 1) degree)
    (target : CoefficientVector (depth + 1) degree)
    (hgood : LiftingGood degree slack depth masks) :
    binarySubsetSum masks
      (powerOfTwoSelector depth degree slack masks target) = target := by
  simp only [powerOfTwoSelector, dif_pos hgood]
  exact recursiveSelector_spec depth degree slack masks target hgood

/-- For every target, the total selector fails only on the explicit recursive rank-failure event. -/
theorem powerOfTwoSelector_failure_le
    (depth degree slack : ℕ)
    (target :
      (Fin (sourceCount depth degree slack) →
        CoefficientVector (depth + 1) degree) →
          CoefficientVector (depth + 1) degree) :
    Pr[(fun masks : Fin (sourceCount depth degree slack) →
          CoefficientVector (depth + 1) degree ↦
        binarySubsetSum masks
            (powerOfTwoSelector depth degree slack masks (target masks)) ≠
          target masks) |
      ($ᵗ (Fin (sourceCount depth degree slack) →
        CoefficientVector (depth + 1) degree))] ≤
      (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
  apply le_trans (probEvent_mono (mx :=
    ($ᵗ (Fin (sourceCount depth degree slack) →
      CoefficientVector (depth + 1) degree))) ?_)
  · exact liftingGood_failure_le degree slack depth
  · intro masks _ hfailure
    by_contra hnotBad
    have hgood : LiftingGood degree slack depth masks := hnotBad
    exact hfailure
      (powerOfTwoSelector_spec_of_good depth degree slack masks (target masks) hgood)

/-- Fixed-target form used by the circular RGSW compiler. -/
theorem powerOfTwoSelector_fixedTarget_failure_le
    (depth degree slack : ℕ)
    (target : CoefficientVector (depth + 1) degree) :
    Pr[(fun masks : Fin (sourceCount depth degree slack) →
          CoefficientVector (depth + 1) degree ↦
        binarySubsetSum masks
            (powerOfTwoSelector depth degree slack masks target) ≠ target) |
      ($ᵗ (Fin (sourceCount depth degree slack) →
        CoefficientVector (depth + 1) degree))] ≤
      (depth + 1 : ℕ) * (2 / (2 : ℝ≥0∞) ^ (slack + 1)) := by
  simpa using powerOfTwoSelector_failure_le depth degree slack (fun _ ↦ target)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting
