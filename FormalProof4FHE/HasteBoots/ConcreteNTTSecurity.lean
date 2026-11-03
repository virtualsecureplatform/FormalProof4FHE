module

public import FormalProof4FHE.HasteBoots.PCSAnalysisField
public import FormalProof4FHE.HasteBoots.PCSParameters
public import FormalProof4FHE.HasteBoots.NativeNTTSecurity

@[expose] public section

/-!
# Main NTT bounds with constructed PCS alphabets and explicit arithmetic losses

The extension field, basis, its auxiliary uniform sampler and both code
distances are supplied by proved constructions. No auxiliary field or basis
certificate is a premise, and no auxiliary sampling is added to the actual
committed verifier program. All arithmetic terms are retained in the explicit
loss. Fresh private coins, native Rust/field refinement, remaining PBS stages,
honest scheduling and production Fiat--Shamir remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.ConcreteNTTSecurity

noncomputable section

open NativeFields NativeNTTRoots PCSAnalysisField

/-- Native k=b repetitions. There are two original-source batches, each using
one shared test and column sample regardless of its repetition count. -/
def arithmetic (q b c r height m queries radius : ℕ) : ENNReal :=
  ((r : ENNReal) / q) ^ b +
    (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / q) ^ b)) +
    2 * PCSParameters.error q b height m queries radius

variable {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [Fintype Digest] [SampleableType Digest]
  {r front suffix m queries height : ℕ} [NeZero m]

section Goldilocks

variable [SampleableType Goldilocks] [SampleableType (Fin 4 → Goldilocks)]
  [SampleableType (Fin r → Goldilocks)] [SampleableType (Fin 4 → Fin r → Goldilocks)]
  [SampleableType (TestMatrix Goldilocks (2 ^ front) 4)] [SampleableType (Fin queries → Fin (2 ^ height))]

/-- Concrete Goldilocks stage: the only PCS premises are validated public
layout/code parameters and radius < (L-m+1)/3. All finite-alphabet obligations
are proved internally, while the complete program and its hash charge persist. -/
theorem goldilocks_soundness_from_empty
    (s : AuthenticatedNTT.Scheme Goldilocks Input Digest Cfg Response Memory CommitMemory 4 8 r 4 front suffix m queries height)
    (dummy : Digest) (enough : m ≤ 2 ^ height) (capacity : 2 ^ suffix ≤ m * 4) (radius : ℕ)
    (small : (radius : ℚ≥0) < (PCSParameters.distance height m : ℚ≥0) / 3) :
    Pr{let outcome ← (AuthenticatedNTT.witness (goldilocksScheme s) dummy)}[
      PackedNTT.FalseRelation goldilocks_packing goldilocksMain s dummy capacity radius outcome.1 ∧
        AuthenticatedNTT.accepted outcome.2.1 = true] ≤
      arithmetic goldilocksModulus 4 8 r height m queries radius +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedNTT.program (goldilocksScheme s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have liftedSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := GoldilocksAlphabet) s.domain) m :
        Set (Fin (2 ^ height) → GoldilocksAlphabet)) : ℚ≥0) / 3 := by
    rwa [PCSParameters.lifted_distance]
  have bound := NativeNTTSecurity.goldilocks_soundness_from_empty (K := GoldilocksAlphabet)
    s goldilocksBasis dummy (by simpa only [Fintype.card_fin] using enough) capacity radius liftedSmall
  simpa only [PCSParameters.error_eq, NativeFields.goldilocks_card, arithmetic,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, two_mul] using bound

end Goldilocks

section BabyBear

variable [SampleableType BabyBear] [SampleableType (Fin 8 → BabyBear)]
  [SampleableType (Fin r → BabyBear)] [SampleableType (Fin 8 → Fin r → BabyBear)]
  [SampleableType (TestMatrix BabyBear (2 ^ front) 8)] [SampleableType (Fin queries → Fin (2 ^ height))]

/-- Concrete BabyBear stage with its degree-eight PCS analysis alphabet;
the lookup extension has no role in this construction or probability loss. -/
theorem babyBear_soundness_from_empty
    (s : AuthenticatedNTT.Scheme BabyBear Input Digest Cfg Response Memory CommitMemory 8 7 r 8 front suffix m queries height)
    (dummy : Digest) (enough : m ≤ 2 ^ height) (capacity : 2 ^ suffix ≤ m * 8) (radius : ℕ)
    (small : (radius : ℚ≥0) < (PCSParameters.distance height m : ℚ≥0) / 3) :
    Pr{let outcome ← (AuthenticatedNTT.witness (babyBearScheme s) dummy)}[
      PackedNTT.FalseRelation babyBear_packing babyBearMain s dummy capacity radius outcome.1 ∧
        AuthenticatedNTT.accepted outcome.2.1 = true] ≤
      arithmetic babyBearModulus 8 7 r height m queries radius +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedNTT.program (babyBearScheme s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have liftedSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := BabyBearAlphabet) s.domain) m :
        Set (Fin (2 ^ height) → BabyBearAlphabet)) : ℚ≥0) / 3 := by
    rwa [PCSParameters.lifted_distance]
  have bound := NativeNTTSecurity.babyBear_soundness_from_empty (K := BabyBearAlphabet)
    s babyBearBasis dummy (by simpa only [Fintype.card_fin] using enough) capacity radius liftedSmall
  simpa only [PCSParameters.error_eq, NativeFields.babyBear_card, arithmetic,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, two_mul] using bound

end BabyBear

end

end FormalProof4FHE.HasteBoots.ConcreteNTTSecurity
