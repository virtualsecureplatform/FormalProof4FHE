module

public import FormalProof4FHE.HasteBoots.AuthenticatedLinear
public import FormalProof4FHE.HasteBoots.PCSAnalysisField
public import FormalProof4FHE.HasteBoots.PCSParameters

@[expose] public section

/-!
# Explicit canonical linear-stage soundness with a constructed PCS alphabet

Every prime base modulus and positive symbol width has the needed analysis
extension and basis. The source count multiplies the PCS error only; the
common-query linear term has no relation-count multiplier. All numeric
arithmetic terms and one complete-program hash charge are retained. This is
the shared private-coin stage, with native/Rust/Fiat--Shamir refinement open.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.ConcreteLinearSecurity

noncomputable section

variable {p count b front suffix m queries height : ℕ} [Fact p.Prime] [NeZero b] [NeZero m]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [Fintype Digest] [SampleableType Digest]
  [SampleableType (Fin b → ZMod p)] [SampleableType (TestMatrix (ZMod p) (2 ^ front) b)]
  [SampleableType (Fin queries → Fin (2 ^ height))]

theorem soundness_from_empty
    (nodesEnough : 2 * b ≤ p)
    (s : AuthenticatedLinear.Scheme (ZMod p) Input Digest Cfg Response Memory CommitMemory count b front suffix m queries height)
    (dummy : Digest) (enough : m ≤ 2 ^ height) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) < (PCSParameters.distance height m : ℚ≥0) / 3) :
    Pr{let outcome ← AuthenticatedLinear.witness (AuthenticatedLinear.nativeScheme p nodesEnough s) dummy}[
      ¬PackedLinear.Holds s.relations (AuthenticatedLinear.sources s dummy capacity radius outcome.1) ∧
        AuthenticatedLinear.accepted outcome.2.1 = true] ≤
      (((front + suffix : ℕ) : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / p) ^ b)) +
        (count : ENNReal) * PCSParameters.error p b height m queries radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedLinear.program (AuthenticatedLinear.nativeScheme p nodesEnough s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have liftedSmall : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := PCSAnalysisField.Alphabet p b) s.domain) m :
        Set (Fin (2 ^ height) → PCSAnalysisField.Alphabet p b)) : ℚ≥0) / 3 := by
    rwa [PCSParameters.lifted_distance]
  have bound := AuthenticatedLinear.native_soundness_from_empty (K := PCSAnalysisField.Alphabet p b)
    p nodesEnough s (PCSAnalysisField.basis p b) dummy
    (by simpa only [Fintype.card_fin] using enough) capacity radius liftedSmall
  simpa [PCSParameters.error_eq, ZMod.card, AuthenticatedLinear.factors, List.sum_ofFn, nsmul_eq_mul] using bound

end

end FormalProof4FHE.HasteBoots.ConcreteLinearSecurity
