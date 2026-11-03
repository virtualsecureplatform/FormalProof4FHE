module

public import FormalProof4FHE.HasteBoots.CommonSourceOpening
public import FormalProof4FHE.HasteBoots.AdaptiveResponse

@[expose] public section

/-!
# Interactive common-source soundness with probabilistic adaptive responses

A uniform matrix is drawn first; an arbitrary response computation runs next;
one fresh shared draw vector is sampled only after that computation returns.
The response result can retain private coins, an oracle cache and any other
state. The near/far bound uses the same single decoded source and the same
maximum of column losses as the deterministic-response theorem. Production
transcript freshness and shared-handler composition remain separate obligations.
-/

open ProbabilityTheory OracleComp

namespace FormalProof4FHE.HasteBoots.CommonSourceOpeningKernel

noncomputable section

variable {F K Row Position Test Output Response : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Row] [Fintype Position] [DecidableEq Position] {m b : ℕ}

/-- Responses and their retained state precede all later column draws. -/
def experiment (b queries : ℕ) [SampleableType (Fin b → Row → F)]
    [SampleableType (Fin queries → Position)]
    (respond : (Fin b → Row → F) → ProbComp Response) :
    ProbComp (((Fin b → Row → F) × Response) × (Fin queries → Position)) := do
  let pair ← AdaptiveResponse.choose ($ᵗ (Fin b → Row → F)) respond
  let draw ← $ᵗ (Fin queries → Position)
  pure (pair, draw)

/-- The far-branch proximity event concerns only the earlier uniform matrix.
Arbitrary later probabilistic response choices cannot inflate its probability. -/
theorem far_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius queries : ℕ) (word : Position → Row → Fin b → F)
    (respond : (Fin b → Row → F) → ProbComp Response)
    (claimed : (Fin b → Row → F) → Response → Position → K)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧ hammingDist word source ≤ radius)
    (coded : ∀ matrix response, claimed matrix response ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m) :
    Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries respond}[
      ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1.1)
        (claimed pair.1.1 pair.1.2) pair.2] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      ColumnOpening.missBound Position queries (radius + 1) := by
  let coins := AdaptiveResponse.choose ($ᵗ (Fin b → Row → F)) respond
  let code := ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m
  have columns := ColumnOpening.adaptive_far_bound coins code
    (fun pair => ProximityOpening.randomWord basis word pair.1)
    (fun pair => claimed pair.1 pair.2) radius queries (fun pair => coded pair.1 pair.2)
  have proximity := (AdaptiveResponse.event_le ($ᵗ (Fin b → Row → F)) respond
    (fun matrix => Code.distFromCode (ProximityOpening.randomWord basis word matrix) code ≤ radius)).trans
      (BaseMatrixProximity.matrix_bound basis domain radius word small far)
  have result := columns.trans (add_le_add proximity le_rfl)
  simpa only [experiment, coins, ColumnOpening.missBound, prEvent_norm] using result

/-- One common source, arbitrary probabilistic adaptive responses, and one
later shared column vector give the proximity term plus the larger column loss. -/
theorem soundness_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius queries : ℕ) (word : Position → Row → Fin b → F)
    (weights : Test → Row → F)
    (respond : (Fin b → Row → F) → ProbComp Response)
    (randomClaim : (Fin b → Row → F) → Response → Position → K)
    (structuredClaim : (Fin b → Row → F) → Response → Test → Position → Fin b → F)
    (finish : (Test → Position → Fin b → F) → Output)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3)
    (randomC : ∀ matrix response, randomClaim matrix response ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m)
    (structuredC : ∀ matrix response test, structuredClaim matrix response test ∈ BlockCode.code domain m b) :
    let source := CommonSource.decode (BlockCode.code domain m b) radius word
    Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries respond}[
      finish (structuredClaim pair.1.1 pair.1.2) ≠
        finish (fun test => StructuredOpening.combine (weights test) source) ∧
      ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1.1)
        (randomClaim pair.1.1 pair.1.2) pair.2 ∧
      ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word)
        (structuredClaim pair.1.1 pair.1.2 test) pair.2] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  dsimp only
  let source := CommonSource.decode (BlockCode.code domain m b) radius word
  let nearEvent := fun (pair : ((Fin b → Row → F) × Response) × (Fin queries → Position)) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠
      finish (fun test => StructuredOpening.combine (weights test) source) ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word)
      (structuredClaim pair.1.1 pair.1.2 test) pair.2
  let randomEvent := fun (pair : ((Fin b → Row → F) × Response) × (Fin queries → Position)) =>
    ColumnOpening.Agrees (ProximityOpening.randomWord basis word pair.1.1)
      (randomClaim pair.1.1 pair.1.2) pair.2
  let event := fun (pair : ((Fin b → Row → F) × Response) × (Fin queries → Position)) =>
    finish (structuredClaim pair.1.1 pair.1.2) ≠
      finish (fun test => StructuredOpening.combine (weights test) source) ∧
    randomEvent pair ∧
    ∀ test, ColumnOpening.Agrees (StructuredOpening.combine (weights test) word)
      (structuredClaim pair.1.1 pair.1.2 test) pair.2
  change Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries respond}[event pair] ≤ _
  by_cases near : ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧ hammingDist word source ≤ radius
  · have decoded := CommonSource.decode_nearby (BlockCode.code domain m b) radius word near
    have bound := StructuredOpening.adaptive_near_falseValue_bound
      (AdaptiveResponse.choose ($ᵗ (Fin b → Row → F)) respond)
      (BlockCode.code domain m b) radius queries word
      (CommonSource.decode (BlockCode.code domain m b) radius word) weights
      (fun pair => structuredClaim pair.1 pair.2) finish decoded.1 decoded.2
      (fun pair test => structuredC pair.1 pair.2 test)
    have normalized :
        Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries respond}[nearEvent pair] ≤
          ColumnOpening.missBound Position queries
            (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius) := by
      simpa only [experiment, nearEvent, source, ColumnOpening.missBound, prEvent_norm] using bound
    have reduced := (prEvent_mono _ event nearEvent (fun pair accepted => ⟨accepted.1, accepted.2.2⟩)).trans normalized
    exact reduced.trans (by
      calc _ = 0 + ColumnOpening.missBound Position queries _ := (zero_add _).symm
           _ ≤ _ := add_le_add zero_le (le_max_left _ _))
  · have bound := far_bound basis domain radius queries word respond randomClaim small near randomC
    have normalized :
        Pr{let pair ← experiment (F := F) (Row := Row) (Position := Position) b queries respond}[randomEvent pair] ≤
          (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
            Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
            ColumnOpening.missBound Position queries (radius + 1) := by
      simpa only [randomEvent] using bound
    exact ((prEvent_mono _ event randomEvent (fun pair accepted => accepted.2.1)).trans normalized).trans
      (add_le_add le_rfl (le_max_right _ _))

end

end FormalProof4FHE.HasteBoots.CommonSourceOpeningKernel
