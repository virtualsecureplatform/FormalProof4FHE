module

public import FormalProof4FHE.HasteBoots.NativeFields
public import FormalProof4FHE.HasteBoots.NTTRootCheck
public import FormalProof4FHE.HasteBoots.PackedNTT

@[expose] public section

/-!
# Checked root towers and the native N=1024 packed profiles

The constants define checked root towers consistent with concrete-ntt's root
construction at locked revision cdeba793e46208320b30d78be19f7be78d49016a.
The main literals match a probe of the existing native plan; their arithmetic
properties are proved independently below. Top roots provide all admissible
power-of-two mathematical domains; the main profile uses literal N=1024 roots
and packing widths 4/8, with k=b repetitions. This does not prove that the
native Tonelli--Shanks/plan/cache implementation returns these constants;
native integer/kernel/Rust refinement remains required.
-/

namespace FormalProof4FHE.HasteBoots.NativeNTTRoots

open NativeFields

def goldilocksTop : Goldilocks := 1753635133440165772
def babyBearTop : BabyBear := 1538287591

theorem goldilocksTop_half : goldilocksTop ^ (2 ^ 31) = -1 := by
  exact goldilocks_top_arithmetic

theorem babyBearTop_half : babyBearTop ^ (2 ^ 26) = -1 := by
  exact babyBear_top_arithmetic

theorem goldilocksTop_primitive : IsPrimitiveRoot goldilocksTop (2 ^ 32) :=
  NTTRootCheck.primitive_of_half_power 31 goldilocksTop goldilocks_odd goldilocksTop_half

theorem babyBearTop_primitive : IsPrimitiveRoot babyBearTop (2 ^ 27) :=
  NTTRootCheck.primitive_of_half_power 26 babyBearTop babyBear_odd babyBearTop_half

/-- The bound is a public parameter condition, unrelated to adversary work. -/
def goldilocksRoot (logSize : ℕ) : Goldilocks := goldilocksTop ^ (2 ^ (31 - logSize))
def babyBearRoot (logSize : ℕ) : BabyBear := babyBearTop ^ (2 ^ (26 - logSize))

theorem goldilocksRoot_primitive (logSize : ℕ) (bound : logSize ≤ 31) :
    IsPrimitiveRoot (goldilocksRoot logSize) (2 ^ (logSize + 1)) := by
  exact goldilocksTop_primitive.pow (by positivity) (by rw [← Nat.pow_add]; congr 1; omega)

theorem babyBearRoot_primitive (logSize : ℕ) (bound : logSize ≤ 26) :
    IsPrimitiveRoot (babyBearRoot logSize) (2 ^ (logSize + 1)) := by
  exact babyBearTop_primitive.pow (by positivity) (by rw [← Nat.pow_add]; congr 1; omega)

def goldilocksMain : Goldilocks := 455906449640507599
def babyBearMain : BabyBear := 812423803

theorem goldilocksMain_tower : goldilocksMain = goldilocksRoot 10 := by
  exact goldilocks_main_arithmetic

theorem babyBearMain_tower : babyBearMain = babyBearRoot 10 := by
  exact babyBear_main_arithmetic

theorem goldilocksMain_primitive : IsPrimitiveRoot goldilocksMain (2 ^ 11) := by
  rw [goldilocksMain_tower]
  exact goldilocksRoot_primitive 10 (by decide)

theorem babyBearMain_primitive : IsPrimitiveRoot babyBearMain (2 ^ 11) := by
  rw [babyBearMain_tower]
  exact babyBearRoot_primitive 10 (by decide)

theorem goldilocksMain_check : NTTRootCheck.check 10 goldilocksMain = true :=
  (NTTRootCheck.check_iff 10 goldilocksMain goldilocks_odd).mpr goldilocksMain_primitive

theorem babyBearMain_check : NTTRootCheck.check 10 babyBearMain = true :=
  (NTTRootCheck.check_iff 10 babyBearMain babyBear_odd).mpr babyBearMain_primitive

theorem goldilocks_packing : 2 ^ 8 * 4 = 2 ^ 10 := by decide
theorem babyBear_packing : 2 ^ 7 * 8 = 2 ^ 10 := by decide

variable {Input Digest Cfg Response Memory CommitMemory : Type} {r front suffix m queries height : ℕ}

/-- Main Goldilocks profile: N=1024, packing 4, eight coefficient variables,
four row repetitions. PCS code-block width and lookup extension stay separate. -/
def goldilocksScheme
    (s : AuthenticatedNTT.Scheme Goldilocks Input Digest Cfg Response Memory CommitMemory 4 8 r 4 front suffix m queries height) :=
  PackedNTT.scheme goldilocks_packing goldilocksMain goldilocksMain_primitive s

/-- Main BabyBear profile: N=1024, packing 8, seven coefficient variables,
eight row repetitions. No caller-supplied transform or primitive-root proof. -/
def babyBearScheme
    (s : AuthenticatedNTT.Scheme BabyBear Input Digest Cfg Response Memory CommitMemory 8 7 r 8 front suffix m queries height) :=
  PackedNTT.scheme babyBear_packing babyBearMain babyBearMain_primitive s

end FormalProof4FHE.HasteBoots.NativeNTTRoots
