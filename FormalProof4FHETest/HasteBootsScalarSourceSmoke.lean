module
import all FormalProof4FHE.HasteBoots.ScalarPublicSourceModel
import all FormalProof4FHE.HasteBoots.ScalarNativeSourceHealing
import all FormalProof4FHETest.HasteBootsScalarCompletedSmoke

namespace FormalProof4FHE.HasteBoots.ScalarSourceSmoke
open scoped BigOperators
open MatrixFold (Cube)
open PackedSumcheckRound (expression)
open NativeExtensionFields (Goldilocks3)
open NativeFieldWire (goldExtensionValue)
open ScalarReplaySmoke (statement proof)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open ScalarCompletedSmoke (execution firstEntry firstMember)
noncomputable section

def oneArity (_ : Unit) := 1
def twoArity (_ : Unit) := 2
def oneCoefficientQ (_ : Unit) : ℚ := 1
def oneCoefficientG (_ : Unit) : Goldilocks3 := 1
def oneIndex (_ : Unit) (_ : Fin (oneArity ())) : Unit := ()
def repeatIndex (_ : Unit) (_ : Fin (twoArity ())) : Unit := ()
def bitTable (_ : Unit) (cell : Cube 1) : ℚ := if cell.1 then 1 else 0

theorem square_expression {R : Type} [CommSemiring R] (values : Unit → R) :
    expression twoArity (fun _ => (1 : R)) repeatIndex values = values () * values () := by
  unfold expression
  rw [Fintype.sum_subsingleton _ ()]
  change (1 : R) * (∏ _j : Fin 2, values ()) = _
  rw [Fin.prod_univ_two, one_mul]

theorem single_expression {R : Type} [CommSemiring R] (values : Unit → R) :
    expression oneArity (fun _ => (1 : R)) oneIndex values = values () := by
  unfold expression
  rw [Fintype.sum_subsingleton _ ()]
  change (1 : R) * (∏ _j : Fin 1, values ()) = _
  rw [Fin.prod_univ_one, one_mul]

theorem square_expressionQ (values : Unit → ℚ) :
    expression twoArity oneCoefficientQ repeatIndex values = values () * values () := square_expression values

theorem single_expressionQ (values : Unit → ℚ) :
    expression oneArity oneCoefficientQ oneIndex values = values () := single_expression values

theorem single_expressionG (values : Unit → Goldilocks3) :
    expression oneArity oneCoefficientG oneIndex values = values () := single_expression values

theorem square_polynomial : ScalarSourcePolynomial.honest twoArity oneCoefficientQ repeatIndex 1 [] bitTable = Polynomial.X^2 := by
  change (∑ suffix : Unit, expression twoArity (fun term => Polynomial.C (oneCoefficientQ term)) repeatIndex
    (fun factor => ScalarSourcePolynomial.linear (bitTable factor (false,suffix)) (bitTable factor (true,suffix)))) = _
  rw [Fintype.sum_subsingleton _ ()]
  simp only [oneCoefficientQ,Polynomial.C_1,square_expression,bitTable,ScalarSourcePolynomial.linear]
  simp [pow_two]

/-- Repeated indices give degree two, not a multilinear interpolation of the
pointwise product's Boolean values. -/
example : (ScalarSourcePolynomial.honest twoArity oneCoefficientQ repeatIndex 1 [] bitTable).natDegree = 2 := by rw [square_polynomial]; simp
example : ScalarSourcePolynomial.truth twoArity oneCoefficientQ repeatIndex 1 [] bitTable = 1 := by
  change (∑ cell : Bool × Unit, expression twoArity oneCoefficientQ repeatIndex (fun factor => bitTable factor cell)) = _
  simp only [square_expressionQ,bitTable]
  simp [Fintype.sum_prod_type]

example : ScalarSourcePolynomial.truth twoArity oneCoefficientQ repeatIndex 1 [2] bitTable = 4 := by
  have identity := ScalarSourcePolynomial.challenge twoArity oneCoefficientQ repeatIndex 1 [] bitTable (by decide) 2
  rw [square_polynomial] at identity
  norm_num at identity
  exact identity.symm

example : ExtensionQuery.evaluate 1 (fun _ => (2 : ℚ)) (fun cell => (bitTable () cell)^2) = 2 := by
  simp [ExtensionQuery.evaluate,bitTable]

example : (ScalarSourcePolynomial.honest twoArity oneCoefficientQ repeatIndex 1 [] bitTable).eval 2 =
    ScalarSourcePolynomial.truth twoArity oneCoefficientQ repeatIndex 1 [2] bitTable :=
  ScalarSourcePolynomial.challenge _ _ _ 1 [] bitTable (by decide) 2

/-- The original fourth packing lane is not discarded as unused padding. -/
def padded (_ : Cube 0) (lane : Fin 4) : ℚ := if lane.val = 3 then 9 else 0
example : ScalarPublicSourceModel.packed (F := ℚ) (K := ℚ) (d := 3) (padding := 1) (c := 2) rfl padded
    (LookupSourceFlattening.split.symm (ExtensionQuery.nativeLanes rfl ⟨3,by decide⟩,())) = 9 := by
  unfold ScalarPublicSourceModel.packed
  simp only [LookupSourceFlattening.flatten, Equiv.apply_symm_apply]
  change (algebraMap ℚ ℚ) (padded () ⟨3,by decide⟩) = 9
  norm_num [padded]

example (point : Fin 2 → ℚ) :
    ScalarSourcePolynomial.truth oneArity oneCoefficientQ oneIndex 2 (List.ofFn point)
      (fun _ => ScalarPublicSourceModel.packed (F := ℚ) (K := ℚ) (d := 3) (padding := 1) (c := 2) rfl padded) =
        ExtensionLookupTerminal.sourceTruth (d := 3) (padding := 1) rfl point padded := by
  have identity := ScalarPublicSourceModel.terminal oneArity oneCoefficientQ oneIndex
    (d := 3) (padding := 1) (c := 2) rfl (fun _ => padded) point
  simpa only [single_expressionQ] using identity

/-- A consistent two-variable original factor: only the (true,true) cell is
one. Its original sum is one; zero messages can heal at the first zero draw. -/
def jointTable (_ : Unit) (cell : Cube 2) : Goldilocks3 := if cell.1 && cell.2.1 then 1 else 0

def sourceTruth := ScalarNativeSourceHealing.truth oneArity oneCoefficientG oneIndex 2 jointTable

theorem initial_truth : sourceTruth [] = 1 := by
  change (∑ cell : Bool × Bool × Unit, expression oneArity oneCoefficientG oneIndex (fun factor => jointTable factor cell)) = _
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Fintype.sum_unique]
  simp [single_expressionG,jointTable]

theorem zero_prefix_truth : sourceTruth [NativeGoldLookup.zero] = 0 := by
  simp only [sourceTruth,ScalarNativeSourceHealing.truth,List.map_cons,List.map_nil,NativeGoldLookup.zero_value]
  simp only [ScalarSourcePolynomial.truth,ScalarSourcePolynomial.fold,single_expressionG,jointTable,MatrixFold.Cube]
  simp

theorem zero_terminal_truth : sourceTruth [NativeGoldLookup.zero,NativeGoldLookup.zero] = 0 := by
  simp only [sourceTruth,ScalarNativeSourceHealing.truth,List.map_cons,List.map_nil,NativeGoldLookup.zero_value]
  simp only [ScalarSourcePolynomial.truth,ScalarSourcePolynomial.fold,single_expressionG,jointTable,MatrixFold.Cube]
  simp

theorem initial_false : ScalarChainHealing.value 0 statement.claims.val ≠ some (sourceTruth []) := by
  have raw : statement.claims.val[0]? = some NativeGoldLookup.zero := by decide +kernel
  simp only [ScalarChainHealing.value,raw,Option.map_some,NativeGoldLookup.zero_value,initial_truth,ne_eq,Option.some.injEq]
  exact zero_ne_one

theorem first_heals : ScalarChainHealing.Healing sourceTruth 0 [] firstEntry := by
  have prior : firstEntry.priorExpected[0]? = some NativeGoldLookup.zero := by decide +kernel
  have next : firstEntry.expected[0]? = some NativeGoldLookup.zero := by decide +kernel
  have challenge : firstEntry.challenge = NativeGoldLookup.zero := by decide +kernel
  constructor
  · simp only [ScalarChainHealing.value,prior,Option.map_some,List.map_nil,initial_truth,NativeGoldLookup.zero_value,
      ne_eq,Option.some.injEq]
    exact zero_ne_one
  · simp only [ScalarChainHealing.value,next,Option.map_some,List.map_nil,List.nil_append,challenge,zero_prefix_truth,NativeGoldLookup.zero_value]

example : ScalarChainHealing.Healing sourceTruth 0 [] firstEntry := first_heals

/-- Healing is a root of the original received polynomial against the honest
source-derived polynomial; every native getter is from the completed record. -/
example : ∃ width : HasteBootsScalarFinishAncestrySmoke.message.evaluations.val.length = ScalarReplaySmoke.info.maxMultiplicands.val + 1,
    let sent := NativeGoldInterpolationPolynomial.polynomial ScalarReplaySmoke.info.maxMultiplicands.val
      HasteBootsScalarFinishAncestrySmoke.message.evaluations.val width
    let honest := ScalarNativeSourceHealing.honest oneArity oneCoefficientG oneIndex 2 jointTable []
    sent.natDegree ≤ 1 ∧ honest.natDegree ≤ 1 ∧ sent ≠ honest ∧
      sent.eval (goldExtensionValue firstEntry.challenge) = honest.eval (goldExtensionValue firstEntry.challenge) := by
  have native := NativeScalarBatchRoundMeaning.initialized_rounds child (NativeScalarBatchWire.bindStatement child statement)
    statement proof rfl 9 worldZero firstEntry firstMember
  exact ScalarNativeSourceHealing.healing_root oneArity oneCoefficientG oneIndex 2 jointTable statement firstEntry native.1
    [] (by decide) 0 ScalarReplaySmoke.info HasteBootsScalarFinishAncestrySmoke.message NativeGoldLookup.zero NativeGoldLookup.zero
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by intro term; exact Nat.le_refl 1) first_heals

/-- The actual initialized native chain cannot make a false equation true
without one of its own completed false-to-true rounds. -/
example : ScalarChainHealing.value 0 (execution 9 worldZero).1.state.expected ≠
      some (sourceTruth ((execution 9 worldZero).1.completed.map (fun entry => entry.challenge))) ∨
    ∃ before entry after, (execution 9 worldZero).1.completed = before ++ entry :: after ∧ ScalarChainHealing.Healing sourceTruth 0 before entry :=
  ScalarNativeSourceHealing.initialized child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl 9 worldZero
    oneArity oneCoefficientG oneIndex 2 jointTable 0 initial_false

/-- If healing were excluded, the same actual terminal equation would remain
false. This implication uses the original chain rather than a supplied trace. -/
example (excluded : ∀ before entry after, (execution 9 worldZero).1.completed = before ++ entry :: after →
    ¬ ScalarChainHealing.Healing sourceTruth 0 before entry) :
    ScalarChainHealing.value 0 (execution 9 worldZero).1.state.expected ≠
      some (sourceTruth ((execution 9 worldZero).1.completed.map (fun entry => entry.challenge))) :=
  ScalarChainHealing.no_healing statement proof _ _
    (NativeScalarBatchHistory.initialized_linked child (NativeScalarBatchWire.bindStatement child statement) statement proof rfl 9 worldZero).1
    sourceTruth 0 initial_false excluded

def claims : List NativeScalarBatchVerifier.SubClaim := (execution 9 worldZero).1.state.expected.map
  (fun expected => ⟨(execution 9 worldZero).1.state.point,expected⟩)

theorem finished : (execution 9 worldZero).1.control = .finished claims := rfl

/-- The consistent original source is truthful at the returned native zero
point despite the false original sum, forcing an actual healing witness. -/
example : ∃ before entry after, (execution 9 worldZero).1.completed = before ++ entry :: after ∧
    ScalarChainHealing.Healing sourceTruth 0 before entry := by
  apply ScalarNativeSourceHealing.terminal_healing child (NativeScalarBatchWire.bindStatement child statement)
    statement proof ScalarReplaySmoke.info rfl rfl 9 worldZero claims finished oneArity oneCoefficientG oneIndex jointTable 0 initial_false
  have getter : (claims[0]?).map NativeScalarBatchVerifier.SubClaim.expected = some NativeGoldLookup.zero := by decide +kernel
  have point : (execution 9 worldZero).1.completed.map (fun entry => entry.challenge) = [NativeGoldLookup.zero,NativeGoldLookup.zero] := by decide +kernel
  have read := congrArg (Option.map goldExtensionValue) getter
  have terminalPoint : (NativeScalarBatchVerifier.execute statement proof 9 (NativeScalarBatchVerifier.initial child statement proof) worldZero).1.completed.map (fun entry => entry.challenge) = [NativeGoldLookup.zero,NativeGoldLookup.zero] := point
  rw [terminalPoint]
  change _ = some (sourceTruth [NativeGoldLookup.zero,NativeGoldLookup.zero])
  rw [zero_terminal_truth]
  simpa only [Option.map_map,Function.comp_def,Option.map_some,NativeGoldLookup.zero_value] using read

end
end FormalProof4FHE.HasteBoots.ScalarSourceSmoke
