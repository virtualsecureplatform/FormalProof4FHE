module
public import FormalProof4FHE.HasteBoots.ScalarChainHealing
public import FormalProof4FHE.HasteBoots.NativeScalarBatchContract
@[expose] public section

/-! Native false-to-true transitions against source-derived honest
polynomials. Degree, recurrence and evaluation properties come from the
original tables and the received native equation, not an honest-poly witness. -/
namespace FormalProof4FHE.HasteBoots.ScalarNativeSourceHealing
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement Info Message)
open NativeScalarBatchPreflight (Proof)
open NativeGoldExtensionArithmetic (Word)
open NativeExtensionFields (Goldilocks3)
open NativeFieldWire (goldExtensionValue)
open MatrixFold (Cube)
noncomputable section
variable {Factor Term : Type} [Fintype Term]

def truth (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (point : List Word) : Goldilocks3 :=
  ScalarSourcePolynomial.truth arity coefficient indices n (point.map goldExtensionValue) tables

def honest (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (point : List Word) : Polynomial Goldilocks3 :=
  ScalarSourcePolynomial.honest arity coefficient indices n (point.map goldExtensionValue) tables

/-- A native passed recurrence at a false source sum forces distinct
polynomials. A subsequent truthful value is their agreement at the actual
retained challenge. The honest polynomial and both degree bounds are derived. -/
theorem root (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (point : List Word) (pending : point.length < n) (info : Info) (message : Message) (prior next challenge : Word)
    (equation : NativeScalarBatchRoundMeaning.Equation info message prior next challenge)
    (bounded : ∀ term, arity term ≤ info.maxMultiplicands.val)
    (falsePrior : goldExtensionValue prior ≠ truth arity coefficient indices n tables point)
    (trueNext : goldExtensionValue next = truth arity coefficient indices n tables (point ++ [challenge])) :
    ∃ width : message.evaluations.val.length = info.maxMultiplicands.val + 1,
      let sent := NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width
      let correct := honest arity coefficient indices n tables point
      sent.natDegree ≤ info.maxMultiplicands.val ∧ correct.natDegree ≤ info.maxMultiplicands.val ∧
        sent ≠ correct ∧ sent.eval (goldExtensionValue challenge) = correct.eval (goldExtensionValue challenge) := by
  obtain ⟨width,degree,checked,evaluated⟩ := equation
  have honestCheck := ScalarSourcePolynomial.check arity coefficient indices n (point.map goldExtensionValue) tables
    (by simpa only [List.length_map] using pending)
  have honestEval := ScalarSourcePolynomial.challenge arity coefficient indices n (point.map goldExtensionValue) tables
    (by simpa only [List.length_map] using pending) (goldExtensionValue challenge)
  have nextTruth : truth arity coefficient indices n tables (point ++ [challenge]) =
      (honest arity coefficient indices n tables point).eval (goldExtensionValue challenge) := by
    simpa only [truth,honest,List.map_append,List.map_cons,List.map_nil] using honestEval.symm
  refine ⟨width,degree,ScalarSourcePolynomial.degree arity coefficient indices _ bounded n _ tables,?_,evaluated.trans (trueNext.trans nextTruth)⟩
  intro equal
  have nodes := congrArg (fun poly : Polynomial Goldilocks3 => poly.eval 0 + poly.eval 1) equal
  rw [checked] at nodes
  exact falsePrior (nodes.trans honestCheck)

/-- Exact original getters select one equation from the actual ordered native
round contract; no polynomial semantics certificate is supplied separately. -/
theorem equation_at (statement : Statement) (entry : NativeScalarBatchVerifier.CompletedRound)
    (meaning : NativeScalarBatchRoundMeaning.RoundMeaning statement entry)
    (slot : ℕ) (info : Info) (message : Message) (prior next : Word)
    (infoAt : statement.infos.val[slot]? = some info) (messageAt : entry.packet.messages.val[slot]? = some message)
    (priorAt : entry.priorExpected[slot]? = some prior) (nextAt : entry.expected[slot]? = some next) :
    NativeScalarBatchRoundMeaning.Equation info message prior next entry.challenge := by
  obtain ⟨infoBound,infoEq⟩ := List.getElem?_eq_some_iff.mp infoAt
  obtain ⟨messageBound,messageEq⟩ := List.getElem?_eq_some_iff.mp messageAt
  obtain ⟨priorBound,priorEq⟩ := List.getElem?_eq_some_iff.mp priorAt
  obtain ⟨nextBound,nextEq⟩ := List.getElem?_eq_some_iff.mp nextAt
  have native := (List.forall₂_iff_get.mp meaning.2.2.2.2).2 slot
    (by simp only [List.length_zip]; omega) (by simp only [List.length_zip]; omega)
  simpa only [List.get_eq_getElem,List.getElem_zip,infoEq,messageEq,priorEq,nextEq] using native

/-- Every native false-to-true source transition is an agreement of the
actual received polynomial with the honest polynomial constructed above. -/
theorem healing_root (arity : Term → ℕ) (coefficient : Term → Goldilocks3)
    (indices : (term : Term) → Fin (arity term) → Factor) (n : ℕ) (tables : Factor → Cube n → Goldilocks3)
    (statement : Statement) (entry : NativeScalarBatchVerifier.CompletedRound)
    (meaning : NativeScalarBatchRoundMeaning.RoundMeaning statement entry)
    (before : List NativeScalarBatchVerifier.CompletedRound) (pending : before.length < n)
    (slot : ℕ) (info : Info) (message : Message) (prior next : Word)
    (infoAt : statement.infos.val[slot]? = some info) (messageAt : entry.packet.messages.val[slot]? = some message)
    (priorAt : entry.priorExpected[slot]? = some prior) (nextAt : entry.expected[slot]? = some next)
    (bounded : ∀ term, arity term ≤ info.maxMultiplicands.val)
    (healing : ScalarChainHealing.Healing (truth arity coefficient indices n tables) slot before entry) :
    ∃ width : message.evaluations.val.length = info.maxMultiplicands.val + 1,
      let sent := NativeGoldInterpolationPolynomial.polynomial info.maxMultiplicands.val message.evaluations.val width
      let correct := honest arity coefficient indices n tables (before.map (fun item => item.challenge))
      sent.natDegree ≤ info.maxMultiplicands.val ∧ correct.natDegree ≤ info.maxMultiplicands.val ∧
        sent ≠ correct ∧ sent.eval (goldExtensionValue entry.challenge) = correct.eval (goldExtensionValue entry.challenge) := by
  have falsePrior : goldExtensionValue prior ≠ truth arity coefficient indices n tables (before.map (fun item => item.challenge)) := by
    intro same
    apply healing.1
    simp only [ScalarChainHealing.value,priorAt,Option.map_some]
    exact congrArg some same
  have trueNext : goldExtensionValue next = truth arity coefficient indices n tables
      (before.map (fun item => item.challenge) ++ [entry.challenge]) := by
    have actual := healing.2
    simp only [ScalarChainHealing.value,nextAt,Option.map_some,Option.some.injEq] at actual
    exact actual
  exact root arity coefficient indices n tables _ (by simpa only [List.length_map] using pending)
    info message prior next entry.challenge (equation_at statement entry meaning slot info message prior next infoAt messageAt priorAt nextAt)
    bounded falsePrior trueNext

/-- The actual initialized scalar chain either remains false at a fixed
original equation or contains an original completed false-to-true transition. -/
theorem initialized (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result) (fuel : ℕ) (world : World)
    (arity : Term → ℕ) (coefficient : Term → Goldilocks3) (indices : (term : Term) → Fin (arity term) → Factor)
    (n : ℕ) (tables : Factor → Cube n → Goldilocks3) (slot : ℕ)
    (initial : ScalarChainHealing.value slot statement.claims.val ≠ some (truth arity coefficient indices n tables [])) :
    ScalarChainHealing.value slot (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected ≠
      some (truth arity coefficient indices n tables ((NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed.map (fun entry => entry.challenge))) ∨
    ∃ before entry after, (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed = before ++ entry :: after ∧
      ScalarChainHealing.Healing (truth arity coefficient indices n tables) slot before entry :=
  ScalarChainHealing.false_or_healing statement proof _ _
    (NativeScalarBatchHistory.initialized_linked transcript result statement proof accepted fuel world).1 _ slot initial

/-- If a returned native terminal equation is truthful despite its false
original claim, the actual chain contains a completed healing round. -/
theorem terminal_healing (transcript result : Transcript) (statement : Statement) (proof : Proof)
    (first : Info) (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok result)
    (head : statement.infos.val.head? = some first) (fuel : ℕ) (world : World) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims)
    (arity : Term → ℕ) (coefficient : Term → Goldilocks3) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Cube first.numVariables.val → Goldilocks3) (slot : ℕ)
    (initial : ScalarChainHealing.value slot statement.claims.val ≠ some (truth arity coefficient indices _ tables []))
    (terminal : (claims[slot]?).map (fun claim => goldExtensionValue claim.expected) =
      some (truth arity coefficient indices _ tables ((NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed.map (fun entry => entry.challenge)))) :
    ∃ before entry after, (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed = before ++ entry :: after ∧
      ScalarChainHealing.Healing (truth arity coefficient indices _ tables) slot before entry := by
  have contract := NativeScalarBatchContract.finished_contract transcript result statement proof first accepted head fuel world claims finished
  have output := (NativeScalarBatchContract.contract_output statement proof first _ claims contract).1
  apply ScalarChainHealing.terminal_true_has_healing statement proof _ _ output _ slot initial
  simpa only [ScalarChainHealing.value,List.getElem?_map,Option.map_map,Function.comp_def] using terminal

end
end FormalProof4FHE.HasteBoots.ScalarNativeSourceHealing
