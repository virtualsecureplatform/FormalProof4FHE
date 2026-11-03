module

public import FormalProof4FHE.HasteBoots.NativeNTTRoots

@[expose] public section

/-!
# Concrete-field authenticated NTT profile bounds

Both N=1024 profiles use proved prime fields and checked literal roots, so
neither primality nor primitive-root/transform correctness is a premise. The
PCS extension/basis, code parameters and fresh private-coin model remain
explicit. The charge belongs to the actual complete committed program.
These are NTT-stage theorems; Rust/optimized field-kernel refinement, remaining
PBS stages, Fiat--Shamir and a concrete total 128-bit work theorem remain open.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.NativeNTTSecurity

noncomputable section

open NativeFields NativeNTTRoots

variable {K Input Digest Cfg Response Memory CommitMemory : Type}
  [Field K] [Fintype K] [DecidableEq K] [DecidableEq Input] [DecidableEq Digest]
  [Fintype Digest] [SampleableType Digest]
  {r front suffix m queries height : ℕ} [NeZero m]

section Goldilocks

variable [Algebra Goldilocks K]
  [SampleableType Goldilocks] [SampleableType (Fin 4 → Goldilocks)]
  [SampleableType (Fin r → Goldilocks)] [SampleableType (Fin 4 → Fin r → Goldilocks)]
  [SampleableType (TestMatrix Goldilocks (2 ^ front) 4)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType ((Fin (2 ^ front) × Fin 4) → K)]

/-- N=1024, b=k=4, c=8, q=18446744069414584321. No supplied field or NTT root
certificate remains, and every repetition shares one batch per original root. -/
theorem goldilocks_soundness_from_empty
    (s : AuthenticatedNTT.Scheme Goldilocks Input Digest Cfg Response Memory CommitMemory 4 8 r 4 front suffix m queries height)
    (basis : Module.Basis (Fin 4) Goldilocks K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * 4) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (AuthenticatedNTT.witness (goldilocksScheme s) dummy)}[
      PackedNTT.FalseRelation goldilocks_packing goldilocksMain s dummy capacity radius outcome.1 ∧
        AuthenticatedNTT.accepted outcome.2.1 = true] ≤
      ((((r : ENNReal) / goldilocksModulus) ^ 4) +
        8 * (((7 : ENNReal) / goldilocksModulus) ^ 4) +
        (JointMatrixOpening.error (K := K) (m := m) (b := 4) (queries := queries) s.domain radius +
          JointMatrixOpening.error (K := K) (m := m) (b := 4) (queries := queries) s.domain radius)) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedNTT.program (goldilocksScheme s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  simpa only [goldilocksScheme, NativeFields.goldilocks_card, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] using
    PackedNTT.soundness_from_empty goldilocks_packing goldilocksMain goldilocksMain_primitive
      s basis dummy enough capacity radius small

end Goldilocks

section BabyBear

variable [Algebra BabyBear K]
  [SampleableType BabyBear] [SampleableType (Fin 8 → BabyBear)]
  [SampleableType (Fin r → BabyBear)] [SampleableType (Fin 8 → Fin r → BabyBear)]
  [SampleableType (TestMatrix BabyBear (2 ^ front) 8)] [SampleableType (Fin queries → Fin (2 ^ height))]
  [SampleableType ((Fin (2 ^ front) × Fin 8) → K)]

/-- N=1024, b=k=8, c=7, q=2013265921. Lookup-extension width is independent
of this packing and of the degree-eight PCS analysis extension. -/
theorem babyBear_soundness_from_empty
    (s : AuthenticatedNTT.Scheme BabyBear Input Digest Cfg Response Memory CommitMemory 8 7 r 8 front suffix m queries height)
    (basis : Module.Basis (Fin 8) BabyBear K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * 8) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (AuthenticatedNTT.witness (babyBearScheme s) dummy)}[
      PackedNTT.FalseRelation babyBear_packing babyBearMain s dummy capacity radius outcome.1 ∧
        AuthenticatedNTT.accepted outcome.2.1 = true] ≤
      ((((r : ENNReal) / babyBearModulus) ^ 8) +
        7 * (((15 : ENNReal) / babyBearModulus) ^ 8) +
        (JointMatrixOpening.error (K := K) (m := m) (b := 8) (queries := queries) s.domain radius +
          JointMatrixOpening.error (K := K) (m := m) (b := 8) (queries := queries) s.domain radius)) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedNTT.program (babyBearScheme s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  simpa only [babyBearScheme, NativeFields.babyBear_card, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat] using
    PackedNTT.soundness_from_empty babyBear_packing babyBearMain babyBearMain_primitive
      s basis dummy enough capacity radius small

end BabyBear

end

end FormalProof4FHE.HasteBoots.NativeNTTSecurity
