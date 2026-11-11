module
public import FormalProof4FHE.HasteBoots.NativeGoldTerminalConstructed
public import FormalProof4FHE.HasteBoots.NativeLookupArithmetic
public import FormalProof4FHE.HasteBoots.ScalarLookupExpression
public import FormalProof4FHE.HasteBoots.NativeHelperPacking
@[expose] public section

/-! Actual successful native terminal folds supply every used decoder, and
actual producer outputs supply their original compression powers. No source
value, decoder-success, or independent raw-power certificate is assumed. -/
namespace FormalProof4FHE.HasteBoots.LookupTerminalDecoding
open scoped BigOperators
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeGoldExtensionArithmetic (Word)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeGoldTerminalQueryMeaning (source compressFrom compress)
noncomputable section

/-- Successful typed zip/fold exposes all used projections. Even zero weights
cannot skip a source decoder. All unmatched-tail issues remain caller shape
obligations; here both lists have their actual common typed count. -/
theorem compressFrom_decodes {padding n count : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3+padding) n)
    (inputs : Fin count → Fin (3+padding) → GoldWord) (weights : Fin count → Word) (out total : Goldilocks3)
    (success : compressFrom query ((List.ofFn (fun i => List.ofFn (inputs i))).zip (List.ofFn weights)) out = some total) :
    ∃ decoded : Fin count → Goldilocks3,
      (∀ i, source query (List.ofFn (inputs i)) = some (decoded i)) ∧
      total = out + ∑ i, goldExtensionValue (weights i) * decoded i := by
  induction count generalizing out with
  | zero =>
    have equal : out = total := Option.some.inj success
    exact ⟨Fin.elim0,(fun i => Fin.elim0 i),by simpa only [Finset.univ_eq_empty,Finset.sum_empty,add_zero] using equal.symm⟩
  | succ count ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.zip_cons_cons,compressFrom,Option.bind_eq_some_iff] at success
    obtain ⟨head,headDecoded,tail⟩ := success
    obtain ⟨remaining,allDecoded,folded⟩ := ih (fun i => inputs i.succ) (fun i => weights i.succ) _ tail
    refine ⟨Fin.cases head remaining,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact headDecoded
      · exact allDecoded j
    · simpa only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,add_assoc] using folded

theorem compress_decodes {padding n count : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3+padding) n)
    (inputs : Fin count → Fin (3+padding) → GoldWord) (weights : Fin count → Word) (total : Goldilocks3)
    (success : compress query (List.ofFn (fun i => List.ofFn (inputs i))) (List.ofFn weights) = some total) :
    ∃ decoded : Fin count → Goldilocks3,
      (∀ i, PaddedExtension.element goldilocksBasis (query.finish (fun lane => goldValue (inputs i lane))) = some (decoded i)) ∧
      total = ∑ i, goldExtensionValue (weights i) * decoded i := by
  obtain ⟨decoded,allDecoded,folded⟩ := compressFrom_decodes query inputs weights 0 total success
  refine ⟨decoded,?_,by simpa only [zero_add] using folded⟩
  intro i
  simpa only [NativeGoldTerminalQueryMeaning.source_ofFn] using allDecoded i

/-- A producer returning a raw output fixes its literal power vector. No
sampler-value witness or canonical representation assumption is needed. -/
theorem produced_powers (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce width rows selection = some output) :
    output.powers = NativeGoldLookup.powers output.y width := by
  unfold NativeGoldLookupProducer.produce at produced
  obtain ⟨pair,_,returned⟩ := Option.bind_eq_some_iff.mp produced
  obtain ⟨y,r⟩ := pair
  dsimp only at returned
  split at returned
  · obtain ⟨inverses,_,same⟩ := Option.map_eq_some_iff.mp returned
    cases same
    rfl
  · contradiction

/-- Exact original field powers and list length are consequences of native
production; later source compression does not choose them independently. -/
theorem produced_power_values (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce width rows selection = some output) :
    output.powers.map goldExtensionValue = List.ofFn (fun i : Fin width => goldExtensionValue output.y ^ i.val) := by
  rw [produced_powers width rows selection output produced,NativeGoldLookup.powers_value,NativeLookupChallenge.powers,
    NativeLookupArithmetic.powersFrom_eq,TupleHash.powers_eq]
  simp only [one_mul]

/-- The complete original point list supplies the same field coordinates to
both scalar truth and the native low-lane/high-row query constructor. -/
theorem fullPoint_ofFn {padding row : ℕ}
    (point : Fin (NativeScalarQueryShape.laneBits (3+padding)+row) → Word)
    (accepted : NativeScalarQueryShape.check row (3+padding) (List.ofFn point).length = true) :
    NativeGoldScalarQueryMeaning.fullPoint row (List.ofFn point) accepted = fun i => goldExtensionValue (point i) := by
  funext i
  simp only [NativeGoldScalarQueryMeaning.fullPoint,List.getElem_ofFn]

theorem pulled_ofFn {padding row : ℕ}
    (point : Fin (NativeScalarQueryShape.laneBits (3+padding)+row) → Word)
    (accepted : NativeScalarQueryShape.check row (3+padding) (List.ofFn point).length = true) :
    NativeGoldTerminalConstructed.pulled row (List.ofFn point) accepted =
      ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
        (fun i => goldExtensionValue (point i)) := by
  unfold NativeGoldTerminalConstructed.pulled
  rw [fullPoint_ofFn]

/-- The original native check supplies all field decoders and its literal
terminal equality, rather than accepting either as an analysis certificate. -/
theorem checked_decodes {padding row count : ℕ}
    (eqPoint point : Fin (NativeScalarQueryShape.laneBits (3+padding)+row) → Word)
    (accepted : NativeScalarQueryShape.check row (3+padding) (List.ofFn point).length = true)
    (logical : NativeUsizeMessage.Usize) (shift : NativeScalarQueryShape.laneBits (3+padding)+row < 64)
    (enough : logical.val ≤ 2^(NativeScalarQueryShape.laneBits (3+padding)+row))
    (r : Word) (inputs : Fin count → Fin (3+padding) → GoldWord) (weights : Fin count → Word) (helper expected : Word)
    (passed : NativeGoldTerminalQuery.constructedCheck row (3+padding) (List.ofFn eqPoint) (List.ofFn point) logical r
      (List.ofFn (fun i => List.ofFn (inputs i))) (List.ofFn weights) helper expected = some true) :
    ∃ decoded : Fin count → Goldilocks3,
      (∀ i, PaddedExtension.element goldilocksBasis
        ((ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
          (fun j => goldExtensionValue (point j))).finish (fun lane => goldValue (inputs i lane))) = some (decoded i)) ∧
      ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
        (goldExtensionValue r) (∑ i, goldExtensionValue (weights i)*decoded i) (goldExtensionValue helper) logical.val enough =
          goldExtensionValue expected := by
  have fieldPassed := (NativeGoldTerminalConstructed.constructedCheck_iff row eqPoint point accepted logical shift enough
    r (List.ofFn (fun i => List.ofFn (inputs i))) (List.ofFn weights) helper expected).mp passed
  rw [NativeGoldTerminalQueryMeaning.value,pulled_ofFn] at fieldPassed
  obtain ⟨total,compressed,equal⟩ := Option.map_eq_some_iff.mp fieldPassed
  obtain ⟨decoded,allDecoded,folded⟩ := compress_decodes _ inputs weights total compressed
  exact ⟨decoded,allDecoded,by simpa only [folded] using equal⟩

/-- Native production also gives a typed view of precisely the original
power list. The field powers and raw list identity are both derived. -/
theorem produced_vector (width : ℕ) (rows : List (List GoldWord))
    (selection : NativeLookupChallenge.Machine Goldilocks3) (output : NativeGoldLookupProducer.Output)
    (produced : NativeGoldLookupProducer.produce width rows selection = some output) :
    ∃ weights : Fin width → Word, output.powers = List.ofFn weights ∧
      ∀ i, goldExtensionValue (weights i) = goldExtensionValue output.y ^ i.val := by
  have mapped := produced_power_values width rows selection output produced
  have length : output.powers.length = width := by
    have counts := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using counts
  let weights : Fin width → Word := fun i => output.powers[i.val]'(by rw [length]; exact i.isLt)
  have rebuilt : List.ofFn weights = output.powers := by
    apply List.ext_getElem (by rw [List.length_ofFn,length])
    intro i leftPresent rightPresent
    simp only [List.getElem_ofFn,weights]
  refine ⟨weights,rebuilt.symm,?_⟩
  rw [← rebuilt,List.map_ofFn] at mapped
  exact fun i => congrFun (List.ofFn_inj.mp mapped) i

/-- The original padded helper coefficient vector decodes to its literal
extension value under the actual coefficient-query post-map, including n=0. -/
theorem helper_decodes {padding n : ℕ} (point : Fin n → Goldilocks3) (helper : Word) :
    PaddedExtension.element goldilocksBasis ((ExtensionQuery.coefficientsQuery goldilocksBasis point).finish
      (NativeHelperPacking.coefficients goldilocksBasis (3+padding) (goldExtensionValue helper))) = some (goldExtensionValue helper) := by
  rw [NativeHelperPacking.coefficients_padded]
  cases n with
  | zero =>
    simp only [ExtensionQuery.coefficientsQuery,ite_true,ExtensionQuery.Broadcast.finish]
    rw [PaddedExtension.multiplication_encode,one_mul,PaddedExtension.element_encode]
  | succ n =>
    simp only [ExtensionQuery.coefficientsQuery,Nat.succ_ne_zero,ite_false,ExtensionQuery.Broadcast.finish,PaddedExtension.element_encode]

end
end FormalProof4FHE.HasteBoots.LookupTerminalDecoding
