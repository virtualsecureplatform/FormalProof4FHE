module
public import FormalProof4FHE.HasteBoots.PackedAccumulatorTrace
public import FormalProof4FHE.HasteBoots.PBSMonomialBlindRotation
@[expose] public section

/-! Composition of the original multiplication sources with the accumulator
constraints. Each multiplication family has its own dimensions and width.
Relations and NTT source bindings are explicit; no native acceptance or
Fiat--Shamir soundness is asserted. -/
namespace FormalProof4FHE.HasteBoots.PackedBlindRotationTrace
open NativeBlindRotation (Cipher Control digit)
open OracleSpec OracleComp
noncomputable section

structure Stages (q log levels monomialCells monomialWidth externalCells externalWidth : ℕ) where
  monomial : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor 1) monomialCells monomialWidth
  monomialAddress : Bool → Fin (2^log) → MatrixFold.Cube monomialCells × Fin monomialWidth
  external : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) externalCells externalWidth
  externalAddress : Bool → Fin (2^log) → MatrixFold.Cube externalCells × Fin externalWidth

variable {q log levels mc mw ec ew : ℕ} [Fact q.Prime]

/-- Bindings to the original factors and results, for both ciphertext halves,
all original digit sources and every gadget level. -/
structure Holds (psi : ZMod q) (bits exponent : ℕ) (control : Control q (2^log) levels)
    (input product difference external : Cipher q (2^log)) (stage : Stages q log levels mc mw ec ew) : Prop where
  monomialRelation : PBSHadamard.Relation stage.monomial
  monomialSource : ∀ half, BlindRotationNTT.transform log psi (input half) =
    PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inl (0,false))
  publicPowers : ∀ half, PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inl (0,true)) =
    BlindRotationMonomial.powers log psi exponent
  monomialResult : ∀ half, BlindRotationNTT.transform log psi (product half) =
    PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inr ())
  externalRelation : PBSHadamard.Relation stage.external
  digits : ∀ half source level, BlindRotationNTT.transform log psi (digit bits level (difference source)) =
    PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))
  keys : ∀ half source level, BlindRotationNTT.transform log psi (control source level half) =
    PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))
  externalResult : ∀ half, BlindRotationNTT.transform log psi (external half) =
    PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inr ())

theorem rotation_of_holds (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (bits exponent : ℕ) (control : Control q (2^log) levels) (input product difference external : Cipher q (2^log))
    (stage : Stages q log levels mc mw ec ew) (holds : Holds psi bits exponent control input product difference external stage) :
    product = fun half => NativeBlindRotation.rotate exponent (input half) :=
  PBSMonomialBlindRotation.rotate_of_relations psi primitive exponent input product stage.monomial stage.monomialAddress
    holds.monomialRelation holds.monomialSource holds.publicPowers holds.monomialResult

theorem external_of_holds (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (bits exponent : ℕ) (control : Control q (2^log) levels) (input product difference external : Cipher q (2^log))
    (stage : Stages q log levels mc mw ec ew) (holds : Holds psi bits exponent control input product difference external stage) :
    external = NativeBlindRotation.externalProduct bits control difference :=
  PBSHadamardBlindRotation.externalProduct_of_relations psi primitive bits control difference external stage.external stage.externalAddress
    holds.externalRelation holds.digits holds.keys holds.externalResult

/-- A failed stage predicate exposes a relation or a specific source binding,
not an assumed coefficient-domain rotation/external-product conclusion. -/
theorem false_stage_coverage (psi : ZMod q) (bits exponent : ℕ) (control : Control q (2^log) levels)
    (input product difference external : Cipher q (2^log)) (stage : Stages q log levels mc mw ec ew)
    (falseStage : ¬Holds psi bits exponent control input product difference external stage) :
    ¬PBSHadamard.Relation stage.monomial ∨
    (∃ half, BlindRotationNTT.transform log psi (input half) ≠ PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inl (0,false))) ∨
    (∃ half, PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inl (0,true)) ≠ BlindRotationMonomial.powers log psi exponent) ∨
    (∃ half, BlindRotationNTT.transform log psi (product half) ≠ PBSMonomialBlindRotation.project stage.monomial (stage.monomialAddress half) (.inr ())) ∨
    ¬PBSHadamard.Relation stage.external ∨
    (∃ half source level, BlindRotationNTT.transform log psi (digit bits level (difference source)) ≠ PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),false))) ∨
    (∃ half source level, BlindRotationNTT.transform log psi (control source level half) ≠ PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) ∨
    (∃ half, BlindRotationNTT.transform log psi (external half) ≠ PBSHadamardBlindRotation.project stage.external (stage.externalAddress half) (.inr ())) := by
  classical
  by_contra absent
  push Not at absent
  exact falseStage ⟨absent.1,absent.2.1,absent.2.2.1,absent.2.2.2.1,absent.2.2.2.2.1,
    absent.2.2.2.2.2.1,absent.2.2.2.2.2.2.1,absent.2.2.2.2.2.2.2⟩

variable {c lanes r : ℕ} {F : Type} [Field F]

def AllHolds (psi : ZMod q) (bits : ℕ) (rounds : PackedAccumulatorTrace.Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r))
    (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (stages : Fin rounds.count → Stages q (c+lanes) levels mc mw ec ew) : Prop :=
  ∀ round, Holds psi bits (controls round).2 (controls round).1
    (tables.input (AccumulatorTrace.active rounds.shape round))
    (tables.product (AccumulatorTrace.active rounds.shape round))
    (tables.difference (AccumulatorTrace.active rounds.shape round))
    (tables.external (AccumulatorTrace.active rounds.shape round)) (stages round)

theorem validTrace (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (embed : ZMod q →+* F) (rounds : PackedAccumulatorTrace.Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (arithmetic : AccumulatorEndpointSoundness.FullHolds (PackedAccumulatorTrace.sources embed rounds tables initial final decompositionA decompositionB))
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (stages : Fin rounds.count → Stages q (c+lanes) levels mc mw ec ew)
    (multiplication : AllHolds psi bits rounds tables controls stages) :
    NativeBlindRotation.ValidTrace bits (List.ofFn controls) initial (List.ofFn (AccumulatorTrace.traceAt rounds.shape tables)) final :=
  PackedAccumulatorTrace.validTrace embed rounds tables initial final decompositionA decompositionB arithmetic bits controls
    (fun round => rotation_of_holds psi primitive bits _ _ _ _ _ _ (stages round) (multiplication round))
    (fun round => external_of_holds psi primitive bits _ _ _ _ _ _ (stages round) (multiplication round))

theorem output_eq_run (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (embed : ZMod q →+* F) (rounds : PackedAccumulatorTrace.Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (arithmetic : AccumulatorEndpointSoundness.FullHolds (PackedAccumulatorTrace.sources embed rounds tables initial final decompositionA decompositionB))
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (stages : Fin rounds.count → Stages q (c+lanes) levels mc mw ec ew)
    (multiplication : AllHolds psi bits rounds tables controls stages) :
    final = NativeBlindRotation.run bits (List.ofFn controls) initial :=
  NativeBlindRotation.validTrace_output bits _ _ _ _
    (validTrace psi primitive embed rounds tables initial final decompositionA decompositionB arithmetic bits controls stages multiplication)

theorem wrong_output_coverage (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (embed : ZMod q →+* F) (rounds : PackedAccumulatorTrace.Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (stages : Fin rounds.count → Stages q (c+lanes) levels mc mw ec ew)
    (wrong : final ≠ NativeBlindRotation.run bits (List.ofFn controls) initial) :
    ¬AccumulatorEndpointSoundness.FullHolds (PackedAccumulatorTrace.sources embed rounds tables initial final decompositionA decompositionB) ∨
      ∃ round, ¬Holds psi bits (controls round).2 (controls round).1
        (tables.input (AccumulatorTrace.active rounds.shape round)) (tables.product (AccumulatorTrace.active rounds.shape round))
        (tables.difference (AccumulatorTrace.active rounds.shape round)) (tables.external (AccumulatorTrace.active rounds.shape round)) (stages round) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (output_eq_run psi primitive embed rounds tables initial final decompositionA decompositionB absent.1 bits controls stages absent.2)

variable [Fintype F] [DecidableEq F] [SampleableType (Fin (2^lanes) → F)]

theorem wrong_output_bound (nodes : PackedSumcheckRound.Node (2^lanes) ↪ F)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (embed : ZMod q →+* F) (rounds : PackedAccumulatorTrace.Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (stages : Fin rounds.count → Stages q (c+lanes) levels mc mw ec ew)
    (multiplication : AllHolds psi bits rounds tables controls stages)
    (wrong : final ≠ NativeBlindRotation.run bits (List.ofFn controls) initial) :
    Pr{let query ← MatrixCompression.sample nodes ((1+r)+c)}[
      AccumulatorEndpointSoundness.FullCheck (PackedAccumulatorTrace.sources embed rounds tables initial final decompositionA decompositionB) query] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card F)^(2^lanes)))) := by
  apply AccumulatorEndpointSoundness.fresh_full_bound nodes
  intro arithmetic
  exact wrong (output_eq_run psi primitive embed rounds tables initial final decompositionA decompositionB arithmetic bits controls stages multiplication)

end
end FormalProof4FHE.HasteBoots.PackedBlindRotationTrace
