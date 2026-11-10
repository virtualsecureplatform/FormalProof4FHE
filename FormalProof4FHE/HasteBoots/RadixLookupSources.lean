module
public import FormalProof4FHE.HasteBoots.RadixTupleHash
public import FormalProof4FHE.HasteBoots.TupleLookupPairOracle
@[expose] public section

/-! Literal radix comparison triples and their source registry. This bridges
canonical digit failure to the existing repeated tuple/reciprocal event. Native
accepted lookup algebra/openings and original owner identification are separate. -/
namespace FormalProof4FHE.HasteBoots.RadixLookupSources
open OracleSpec OracleComp BinaryTree
open scoped Matrix
noncomputable section
variable {p radix d b n : ℕ}

/-- Native order is digit-major and incoming-borrow-minor, with 2*radix rows. -/
def publicTable (p radix bound : ℕ) : Fin (radix*2) → Fin 3 → ZMod p :=
  fun index => RadixTupleHash.row p radix bound (finProdFinEquiv.symm index)

theorem mem_public_iff (p radix bound : ℕ) (candidate : Fin 3 → ZMod p) :
    candidate ∈ RadixCanonicity.table p radix bound ↔ ∃ index, candidate = publicTable p radix bound index := by
  constructor
  · intro member
    obtain ⟨digit,incoming,equal⟩ := (RadixCanonicity.mem_table_iff p radix bound candidate).mp member
    refine ⟨finProdFinEquiv (digit,incoming),?_⟩
    simpa only [publicTable,Equiv.symm_apply_apply,RadixTupleHash.row] using equal
  · rintro ⟨index,equal⟩
    apply (RadixCanonicity.mem_table_iff p radix bound candidate).mpr
    exact ⟨(finProdFinEquiv.symm index).1,(finProdFinEquiv.symm index).2,equal⟩

def tuple (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (limb : Fin d) (cell : MatrixFold.Cube n) (lane : Fin b) : Fin 3 → ZMod p :=
  ![registry (DecompositionLinear.digit limb) cell lane,
    registry (DecompositionLinear.borrow limb.castSucc) cell lane,
    registry (DecompositionLinear.borrow limb.succ) cell lane]

/-- The comparison backend omits only the input column. Its registry has
all digits followed by all d+1 borrows, in the original native order. -/
def comparisonRegistry {Value : Type} (registry : Fin (2*d+2) → Value) : Fin (2*d+1) → Value :=
  fun index => registry ⟨index.val+1,by have := index.isLt; omega⟩

def comparisonSlots (limb : Fin d) : Fin 3 → Fin (2*d+1) :=
  ![⟨limb.val,by have := limb.isLt; omega⟩,
    ⟨d+limb.val,by have := limb.isLt; omega⟩,
    ⟨d+limb.val+1,by have := limb.isLt; omega⟩]

theorem tuple_comparisonRegistry (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (limb : Fin d) (cell : MatrixFold.Cube n) (lane : Fin b) :
    (fun slot => comparisonRegistry registry (comparisonSlots limb slot) cell lane) = tuple registry limb cell lane := by
  funext slot
  fin_cases slot
  all_goals simp only [comparisonRegistry,comparisonSlots,tuple]
  all_goals apply congrArg (fun factor => registry factor cell lane)
  all_goals apply Fin.ext
  all_goals simp [DecompositionLinear.digit,DecompositionLinear.borrow,Fin.val_castSucc,Fin.val_succ]
  all_goals omega

theorem lookup_iff (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) :
    RadixCanonicity.LookupAt p radix registry cell lane ↔
      ∀ limb, ∃ index, tuple registry limb cell lane = publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val) index := by
  simp only [RadixCanonicity.LookupAt,mem_public_iff,tuple]

/-- One noncanonical active coefficient exposes a particular failed comparison
on original columns, unless the authenticated reconstruction/endpoints fail. -/
theorem failure_coverage [Fact p.Prime]
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p-1 < radix^d)
    (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) (wrong : ¬RadixCanonicity.CanonicalAt p radix registry cell lane) :
    ¬DecompositionLinear.Relation (radix : ZMod p) registry ∨
      ∃ limb, ∀ index, tuple registry limb cell lane ≠ publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val) index := by
  rcases RadixCanonicity.failure_dichotomy radixLarge radixSmall enough registry cell lane wrong with linear | bad
  · exact Or.inl linear
  · obtain ⟨limb,outside⟩ := bad
    refine Or.inr ⟨limb,?_⟩
    intro index equal
    exact outside ((mem_public_iff p radix _ _).mpr ⟨index,equal⟩)

/-- Wrong individual digits are covered even when their integer weighted sum
already equals the canonical input (an out-of-range digit can carry a radix). -/
theorem digit_failure_coverage [Fact p.Prime]
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p-1 < radix^d)
    (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (cell : MatrixFold.Cube n) (lane : Fin b) (digit : Fin d)
    (wrong : (registry (DecompositionLinear.digit digit) cell lane).val ≠
      (registry DecompositionLinear.input cell lane).val / radix^digit.val % radix) :
    ¬DecompositionLinear.Relation (radix : ZMod p) registry ∨
      ∃ limb, ∀ index, tuple registry limb cell lane ≠ publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val) index := by
  classical
  by_cases linear : DecompositionLinear.Relation (radix : ZMod p) registry
  · right
    have failed : ¬RadixCanonicity.LookupAt p radix registry cell lane :=
      fun checked => wrong (RadixCanonicity.digits_of_constraints radixLarge radixSmall enough registry linear cell lane checked digit)
    rw [lookup_iff] at failed
    push Not at failed
    exact failed
  · exact Or.inl linear

variable {active : ℕ}
def sources (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (address : Fin active → MatrixFold.Cube n × Fin b) (limb : Fin d) : Fin active → Fin 3 → ZMod p :=
  fun position => tuple registry limb (address position).1 (address position).2

theorem noncanonical_exposes_comparison [Fact p.Prime]
    (radixLarge : 1 < radix) (radixSmall : radix < p) (enough : p-1 < radix^d)
    (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (address : Fin active → MatrixFold.Cube n × Fin b)
    (linear : DecompositionLinear.Relation (radix : ZMod p) registry)
    (wrong : ∃ position, ¬RadixCanonicity.CanonicalAt p radix registry (address position).1 (address position).2) :
    ∃ limb, ∃ position, ∀ index, sources registry address limb position ≠ publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val) index := by
  obtain ⟨position,bad⟩ := wrong
  rcases failure_coverage radixLarge radixSmall enough registry _ _ bad with failed | comparison
  · exact (failed linear).elim
  · obtain ⟨limb,outside⟩ := comparison
    exact ⟨limb,position,outside⟩

variable [Fact p.Prime] {K Later Cfg Input Digest Payload : Type}
  [Field K] [Algebra (ZMod p) K] [CharP K p] [Fintype K] [DecidableEq K] [SampleableType K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Full tuple-hash plus reciprocal error, independently repeated, retained
through arbitrary later shared calls. This bounds the semantic AllPass event;
actual lookup acceptance must still be reduced to it and its algebra/PCS errors. -/
theorem comparison_bound
    (registry : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod p)
    (address : Fin active → MatrixFold.Cube n × Fin b) (limb : Fin d)
    (multiplicities : Fin (radix*2) → K)
    (bad : ∃ position, ∀ index, sources registry address limb position ≠ publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val) index)
    (small : active < p) (repetitions : ℕ)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : Option (List (K × K)) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program
        (PrivateSampling.embed Cfg Input Digest (TupleLookupPair.repeats (K := K)
          (publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val)) repetitions).run) next)).run state}[
      outcome.1.1.elim False (TupleLookupPair.AllPass (sources registry address limb)
        (publicTable p radix (RadixCanonicity.modulusDigit p radix limb.val)) multiplicities)] ≤
      TupleLookupPair.error (Fintype.card K) 3 active (radix*2) ^ repetitions :=
  TupleLookupPairOracle.retained_bound enc dummy shape (sources registry address limb) _ multiplicities bad small repetitions next state

end
end FormalProof4FHE.HasteBoots.RadixLookupSources
