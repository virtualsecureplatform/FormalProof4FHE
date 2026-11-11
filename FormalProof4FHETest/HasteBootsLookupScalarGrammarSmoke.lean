module
import all FormalProof4FHE.HasteBoots.LookupScalarGrammar
import all FormalProof4FHE.HasteBoots.AllocatedScalarHelper
import all FormalProof4FHETest.HasteBootsSourceFrontierSmoke
import Mathlib.Tactic.ComputeDegree

namespace FormalProof4FHE.HasteBoots.LookupScalarGrammarSmoke
open scoped BigOperators
open MatrixFold (Cube)
open ExtensionLookupIdentity (Factor)
open Polynomial
open HasteBootsBatchMeaningSmoke (usize)
noncomputable section

def bits (cell : Cube 1) : ℚ := if cell.1 then 1 else 0
def source (_ : Fin 1) := bits
def eqPoint (_ : Fin 1) : ℚ := 1

def full := ScalarSourcePolynomial.honest ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
  ExtensionLookupIdentity.fullIndices 1 [] (LookupPairArithmetic.fullTables eqPoint 1 0 source bits)
def partialIdentity := ScalarSourcePolynomial.honest ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient (1 : ℚ))
  ExtensionLookupIdentity.partialIndices 1 [] (ExtensionLookupIdentity.factors eqPoint 0 source bits 1)

private theorem full_expressionP (values : Factor → ℚ[X]) :
    PackedSumcheckRound.expression ExtensionLookupIdentity.fullArity
      (fun term => C (ExtensionLookupIdentity.fullCoefficient term)) ExtensionLookupIdentity.fullIndices values =
        values .eq * values .helper * values .hash - values .eq := by
  unfold PackedSumcheckRound.expression
  rw [show (Finset.univ : Finset ExtensionLookupIdentity.FullTerm) = {.product,.subtractOne} from rfl]
  simp [ExtensionLookupIdentity.fullArity,ExtensionLookupIdentity.fullCoefficient,ExtensionLookupIdentity.fullIndices]
  change (∏ j : Fin 3, values (![Factor.eq,.helper,.hash] j)) + -values .eq ^ (Finset.univ : Finset (Fin 1)).card = _
  simp [Fin.prod_univ_succ,mul_assoc,sub_eq_add_neg]

private theorem partial_expressionP (values : Factor → ℚ[X]) :
    PackedSumcheckRound.expression ExtensionLookupIdentity.partialArity
      (fun term => C (ExtensionLookupIdentity.partialCoefficient (1 : ℚ) term)) ExtensionLookupIdentity.partialIndices values =
        values .eq * (values .helper + values .mask * values .hash * values .helper - values .mask) := by
  unfold PackedSumcheckRound.expression
  rw [show (Finset.univ : Finset ExtensionLookupIdentity.PartialTerm) = {.reciprocal,.product,.subtractMask} from rfl]
  simp [ExtensionLookupIdentity.partialArity,ExtensionLookupIdentity.partialCoefficient,ExtensionLookupIdentity.partialIndices]
  change (∏ j : Fin 2, values (![Factor.eq,.helper] j)) +
    ((∏ j : Fin 4, values (![Factor.eq,.mask,.hash,.helper] j)) -
    (∏ j : Fin 2, values (![Factor.eq,.mask] j))) = _
  simp [Fin.prod_univ_succ]
  ring

private theorem eq_false : PackedEqualityCube.weight eqPoint (false,()) = 0 := by
  have last := PackedEqualityCube.weight_zero (fun i : Fin 0 => eqPoint i.succ) ()
  have step := PackedEqualityCube.weight_succ (n := 0) eqPoint false ()
  exact step.trans ((congrArg (fun value : ℚ => (1-eqPoint 0)*value) last).trans (by norm_num [eqPoint]))
private theorem eq_true : PackedEqualityCube.weight eqPoint (true,()) = 1 := by
  have last := PackedEqualityCube.weight_zero (fun i : Fin 0 => eqPoint i.succ) ()
  have step := PackedEqualityCube.weight_succ (n := 0) eqPoint true ()
  exact step.trans ((congrArg (fun value : ℚ => eqPoint 0*value) last).trans (by norm_num [eqPoint]))
private theorem mask_false : ExtensionLookupIdentity.maskTable (n := 1) 1 (false,()) = (1 : ℚ) := by decide +kernel
private theorem mask_true : ExtensionLookupIdentity.maskTable (n := 1) 1 (true,()) = (0 : ℚ) := by decide +kernel

/-- Actual source/helper/EQ factors give a cubic full-table polynomial. -/
theorem full_polynomial : full = X^3+X^2-X := by
  change (∑ suffix : Unit, PackedSumcheckRound.expression ExtensionLookupIdentity.fullArity
    (fun term => C (ExtensionLookupIdentity.fullCoefficient term)) ExtensionLookupIdentity.fullIndices
    (fun factor => ScalarSourcePolynomial.linear
      (LookupPairArithmetic.fullTables eqPoint 1 0 source bits factor (false,suffix))
      (LookupPairArithmetic.fullTables eqPoint 1 0 source bits factor (true,suffix)))) = _
  rw [Fintype.sum_subsingleton _ ()]
  rw [full_expressionP]
  simp [ScalarSourcePolynomial.linear,LookupPairArithmetic.fullTables,ExtensionLookupIdentity.factors,ExtensionLookupIdentity.hashTable,
    TupleHash.hash_eq_sum,source,bits,eq_false,eq_true]
  ring

/-- The active-prefix mask remains its own factor, giving degree four. -/
theorem partial_polynomial : partialIdentity = -X^4+X^3+2*X^2-X := by
  change (∑ suffix : Unit, PackedSumcheckRound.expression ExtensionLookupIdentity.partialArity
    (fun term => C (ExtensionLookupIdentity.partialCoefficient (1 : ℚ) term)) ExtensionLookupIdentity.partialIndices
    (fun factor => ScalarSourcePolynomial.linear
      (ExtensionLookupIdentity.factors eqPoint 0 source bits 1 factor (false,suffix))
      (ExtensionLookupIdentity.factors eqPoint 0 source bits 1 factor (true,suffix)))) = _
  rw [Fintype.sum_subsingleton _ ()]
  rw [partial_expressionP]
  simp [ScalarSourcePolynomial.linear,ExtensionLookupIdentity.factors,ExtensionLookupIdentity.hashTable,mask_false,mask_true,
    TupleHash.hash_eq_sum,source,bits,eq_false,eq_true]
  ring

example : full.natDegree = 3 := by rw [full_polynomial]; compute_degree <;> norm_num
example : partialIdentity.natDegree = 4 := by rw [partial_polynomial]; compute_degree <;> norm_num
example : full.eval 2 = 10 ∧ partialIdentity.eval 2 = -2 := by rw [full_polynomial,partial_polynomial]; norm_num

example (point : Fin 1 → ℚ) :
    ScalarSourcePolynomial.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      1 (List.ofFn point) (fun _ => bits) = ExtensionQuery.evaluate 1 point bits :=
  ScalarLookupExpression.sum_terminal bits point

/-- A helper's fourth coefficient lane is not a fourth scalar coordinate. -/
def helperPadding (_ : Cube 0) (lane : Fin 4) : NativeFields.Goldilocks := if lane.val = 3 then 9 else 0

theorem helper_decoded : PaddedExtension.decode (padding := 1) NativeExtensionFields.goldilocksBasis (helperPadding ()) = 0 := by
  have coordinates : (fun i : Fin 3 => helperPadding () (i.castAdd 1)) = 0 := by
    funext i
    simp only [helperPadding,Fin.val_castAdd,Pi.zero_apply]
    have different : i.val ≠ 3 := by omega
    simp only [different,ite_false]
  change NativeExtensionFields.goldilocksBasis.equivFun.symm (fun i : Fin 3 => helperPadding () (i.castAdd 1)) = 0
  rw [coordinates,map_zero]

example : (ExtensionQuery.coefficientsQuery NativeExtensionFields.goldilocksBasis (Fin.elim0 : Fin 0 → NativeExtensionFields.Goldilocks3)).evaluate helperPadding =
    PaddedExtension.encode (padding := 1) NativeExtensionFields.goldilocksBasis 0 := by
  rw [ExtensionQuery.coefficients_evaluate]
  exact congrArg (PaddedExtension.encode NativeExtensionFields.goldilocksBasis) helper_decoded

/-- Source packing reads that same fourth lane at the lane-three Boolean
point, so substituting source flattening for helper decoding changes meaning. -/
example : ScalarPublicSourceModel.packed (F := NativeFields.Goldilocks) (K := NativeExtensionFields.Goldilocks3)
    (d := 3) (padding := 1) (c := 2) rfl helperPadding
      (LookupSourceFlattening.split.symm (ExtensionQuery.nativeLanes rfl ⟨3,by decide⟩,())) = 9 := by
  unfold ScalarPublicSourceModel.packed
  simp only [LookupSourceFlattening.flatten,Equiv.apply_symm_apply]
  change (algebraMap NativeFields.Goldilocks NativeExtensionFields.Goldilocks3) 9 = 9
  exact map_ofNat _ _

/-- Source width four and helper width eight share the same two-coordinate
scalar point; coefficient decoding does not create five extra coordinates. -/
example (eqPoint point : Fin 2 → NativeExtensionFields.Goldilocks3) (r y : NativeExtensionFields.Goldilocks3)
    (sources : Fin 1 → Cube 0 → Fin 4 → NativeFields.Goldilocks)
    (helpers : Cube 2 → Fin 8 → NativeFields.Goldilocks) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
      ExtensionLookupIdentity.partialIndices 2 (List.ofFn point)
      (ExtensionLookupIdentity.factors eqPoint y (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) rfl (sources column))
        (fun cell => PaddedExtension.decode (padding := 5) NativeExtensionFields.goldilocksBasis (helpers cell)) 3) =
      ExtensionLookupIdentity.terminal eqPoint point r
        (∑ column : Fin 1, y^column.val * ExtensionLookupTerminal.sourceTruth (d := 3) (padding := 1) (c := 2) (row := 0) rfl point (sources column))
        (ExtensionQuery.evaluate 2 point (fun cell => PaddedExtension.decode (padding := 5) NativeExtensionFields.goldilocksBasis (helpers cell))) 3 (by decide) :=
  ScalarLookupExpression.packed_partial_terminal (d := 3) (sourcePadding := 1) (helperPadding := 5) (c := 2) (row := 0) NativeExtensionFields.goldilocksBasis rfl eqPoint point r y sources helpers 3 (by decide)

example (eqPoint point : Fin 2 → NativeExtensionFields.Goldilocks3) (r y : NativeExtensionFields.Goldilocks3)
    (sources : Fin 1 → Cube 0 → Fin 4 → NativeFields.Goldilocks)
    (helpers : Cube 2 → Fin 8 → NativeFields.Goldilocks) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices 2 (List.ofFn point)
      (LookupPairArithmetic.fullTables eqPoint r y (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) rfl (sources column))
        (fun cell => PaddedExtension.decode (padding := 5) NativeExtensionFields.goldilocksBasis (helpers cell))) =
      ExtensionLookupIdentity.terminal eqPoint point r
        (∑ column : Fin 1, y^column.val * ExtensionLookupTerminal.sourceTruth (d := 3) (padding := 1) (c := 2) (row := 0) rfl point (sources column))
        (ExtensionQuery.evaluate 2 point (fun cell => PaddedExtension.decode (padding := 5) NativeExtensionFields.goldilocksBasis (helpers cell))) 4 le_rfl :=
  ScalarLookupExpression.packed_full_terminal (d := 3) (sourcePadding := 1) (helperPadding := 5) (c := 2) (row := 0) NativeExtensionFields.goldilocksBasis rfl eqPoint point r y sources helpers

/-- The sum-check claim and original coefficient opening use one row point. -/
example (point : Fin 2 → NativeExtensionFields.Goldilocks3)
    (helpers : Cube 2 → Fin 8 → NativeFields.Goldilocks) (claim : Fin 8 → NativeFields.Goldilocks)
    (value expected : NativeExtensionFields.Goldilocks3)
    (decoded : PaddedExtension.element NativeExtensionFields.goldilocksBasis
      ((ExtensionQuery.coefficientsQuery (padding := 5) NativeExtensionFields.goldilocksBasis point).finish claim) = some value)
    (matched : expected = value) :
    expected = ScalarSourcePolynomial.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      2 (List.ofFn point) (fun _ cell => PaddedExtension.decode (padding := 5) NativeExtensionFields.goldilocksBasis (helpers cell)) ∨
      claim ≠ (ExtensionQuery.coefficientsQuery (padding := 5) NativeExtensionFields.goldilocksBasis point).query.fold helpers :=
  ScalarLookupExpression.sum_checked_or_wrong (padding := 5) NativeExtensionFields.goldilocksBasis point helpers claim value expected decoded matched

def request (logical repetitions : ℕ) : NativeSharedLookupStatement.Request :=
  ⟨1,[],repetitions,⟨[0],usize logical⟩⟩

/-- Full and partial metadata differ at the original literal length test. -/
example : (NativeSharedLookupStatement.infos (usize 2) [request 4 2,request 3 1]).map (fun info => info.maxMultiplicands.val) = [1,3,1,3,1,4] := by decide +kernel
example : LookupScalarGrammar.identityInfo (usize 2) (request 4 1) = ⟨usize 3,usize 2⟩ := by decide +kernel
example : LookupScalarGrammar.identityInfo (usize 2) (request 3 1) = ⟨usize 4,usize 2⟩ := by decide +kernel
example (term : ExtensionLookupIdentity.FullTerm) : ExtensionLookupIdentity.fullArity term ≤
    (LookupScalarGrammar.identityInfo (usize 2) (request 4 1)).maxMultiplicands.val :=
  LookupScalarGrammar.full_arity _ _ rfl term
example (term : ExtensionLookupIdentity.PartialTerm) : ExtensionLookupIdentity.partialArity term ≤
    (LookupScalarGrammar.identityInfo (usize 2) (request 3 1)).maxMultiplicands.val :=
  LookupScalarGrammar.partial_arity _ _ (by decide +kernel) term

/-- A completed native prelude supplies original sum/identity slots directly;
no separate tags, polynomial degrees, or initial-claims witness is supplied. -/
example {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → NativeSharedLookupStatement.Request)
    (n : NativeUsizeMessage.Usize) (multiplicities : List (List NativeFieldRepresentation.GoldWord))
    (roots : List NativeRootMessage.Digest) (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ)
    (transcript : NativeTranscript.Transcript) (world : InputIndexedOracle.World) (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready) (index : ℕ) (present : index < ready.jobs.length) :
    ready.statement.infos.val[2*index]? = some (LookupScalarGrammar.sumInfo n) ∧
      ready.statement.infos.val[2*index+1]? = some (LookupScalarGrammar.identityInfo n (ready.jobs[index]).tag.request) := by
  have pair := LookupScalarGrammar.protocol_pair fits requests n multiplicities roots rootFits w lookupFuel equalityFuel transcript world ready success index present
  exact ⟨pair.1,pair.2.1⟩

end
end FormalProof4FHE.HasteBoots.LookupScalarGrammarSmoke
