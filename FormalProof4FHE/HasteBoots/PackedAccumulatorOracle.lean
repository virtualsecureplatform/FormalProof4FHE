module
public import FormalProof4FHE.HasteBoots.AccumulatorEndpointSoundness
public import FormalProof4FHE.HasteBoots.PreparedTerminal
@[expose] public section

/-! The accumulator's actual seven-source common-query arithmetic check.
Query lists keep their native order; no shifted or duplicated source is committed. -/
namespace FormalProof4FHE.HasteBoots.PackedAccumulatorOracle
open OracleSpec OracleComp Matrix
open PackedSumcheckSubclaim (Query)
open AccumulatorMatrixSoundness (Sources Table selectedQuery shiftedQueries correction)
open AccumulatorEndpointSoundness (rowQuery expected FullHolds FullCheck)
noncomputable section
variable {F Memory Cfg Input Digest Payload : Type} [Field F] [DecidableEq F] {b c r : ℕ}

abbrev Values (F : Type) (b : ℕ) := Fin 7 → List (Fin b → F)

structure Context (F : Type) (b c r : ℕ) where
  initial : Bool → MatrixFold.Cube c → Fin b → F
  final : Bool → MatrixFold.Cube c → Fin b → F
  start : MatrixFold.Cube r
  finish : MatrixFold.Cube r

def context (sources : Sources F b c r) : Context F b c r :=
  ⟨sources.initial,sources.final,sources.start,sources.finish⟩

/-- Native indices: input, monomial product, difference, output, sum product,
and the two existing decomposition input sources. -/
def source (sources : Sources F b c r) : Fin 7 → Table F b c r :=
  ![sources.input,sources.product,sources.difference,sources.output,sources.external,sources.duplicateA,sources.duplicateB]

def queries (ctx : Context F b c r) (query : Query F b ((1+r)+c)) (factor : Fin 7) : List (Query F b ((1+r)+c)) :=
  if factor = 0 then query :: rowQuery query (AccumulatorShiftQueries.zero r) :: shiftedQueries query
  else if factor = 2 then [query,selectedQuery query false,selectedQuery query true]
  else if factor = 3 then [query,rowQuery query ctx.finish]
  else [query]

def value (values : Values F b) (factor : Fin 7) (index : ℕ) : Fin b → F :=
  (values factor)[index]?.getD 0

/-- Length checks precede all accesses, matching rejection before arithmetic
or opening work on malformed source/value families. -/
def Check (ctx : Context F b c r) (query : Query F b ((1+r)+c)) (values : Values F b) : Prop :=
  (∀ factor, (values factor).length = (queries ctx query factor).length) ∧
  value values 2 0 = value values 1 0-value values 0 0 ∧
  value values 3 0 = value values 0 0+value values 4 0 ∧
  value values 2 1 = value values 5 0 ∧
  value values 2 2 = value values 6 0 ∧
  value values 0 1 = expected query ctx.initial ∧
  value values 3 1 = expected query ctx.final ∧
  ((values 0).drop 2).sum - value values 3 0 =
    correction query ctx.start ctx.initial-correction query ctx.finish ctx.final

instance checkDecidable (ctx : Context F b c r) (query : Query F b ((1+r)+c)) (values : Values F b) :
    Decidable (Check ctx query values) := by
  unfold Check
  infer_instance

def check (ctx : Context F b c r) (query : Query F b ((1+r)+c)) (values : Values F b) : Bool :=
  decide (Check ctx query values)

structure Packet (F Memory : Type) (b c r : ℕ) where
  query : Query F b ((1+r)+c)
  values : Values F b
  memory : Memory
  accepted : Bool

def packet (ctx : Context F b c r)
    (result : Query F b ((1+r)+c) × Values F b × Memory) : Packet F Memory b c r :=
  ⟨result.1,result.2.1,result.2.2,check ctx result.1 result.2.1⟩

def disabled (memory : Memory) : Packet F Memory b c r :=
  ⟨PreparedTerminal.zeroQuery _,fun _ => [],memory,false⟩

def Truthful (sources : Sources F b c r) (result : Packet F Memory b c r) : Prop :=
  result.accepted = true ∧ ∀ factor,
    result.values factor = (queries (context sources) result.query factor).map (fun query => query.fold (source sources factor))

/-- All seven computed arithmetic identities reduce to the already proved
fixed-source residuals when the supplied lists are truthful. -/
theorem truthful_check (sources : Sources F b c r) (query : Query F b ((1+r)+c)) (values : Values F b)
    (truthful : ∀ factor, values factor = (queries (context sources) query factor).map (fun query => query.fold (source sources factor)))
    (checked : check (context sources) query values = true) : FullCheck sources query := by
  have arithmetic : Check (context sources) query values := of_decide_eq_true checked
  rcases arithmetic with ⟨_,difference,output,duplicateA,duplicateB,initial,final,continuity⟩
  have same : values = fun factor => (queries (context sources) query factor).map (fun query => query.fold (source sources factor)) := funext truthful
  subst values
  simp [value,queries,context,source] at difference output duplicateA duplicateB initial final continuity
  exact ⟨⟨difference,output,duplicateA,duplicateB,continuity⟩,initial,final⟩

omit [DecidableEq F] in
/-- Checked list lengths turn pointwise batch values into the exact returned
list, without assuming consistency between duplicated query positions. -/
theorem values_eq (left right : List (Fin b → F)) (length : left.length = right.length)
    (correct : ∀ index : Fin right.length, left[index.val]?.getD 0 = right.get index) : left = right := by
  apply List.ext_getElem length
  intro index leftBound rightBound
  have same := correct ⟨index,rightBound⟩
  simpa only [List.getElem?_eq_getElem leftBound,Option.getD_some,List.get_eq_getElem] using same

variable [SampleableType (Fin b → F)]

def program (nodes : PackedSumcheckRound.Node b ↪ F) (ctx : Context F b c r)
    (enabled : Bool) (before : OracleComp (SharedSequence.Shared Cfg Input Digest) Memory)
    (receive : Memory → Query F b ((1+r)+c) → OracleComp (SharedSequence.Shared Cfg Input Digest) (Values F b × Memory))
    (fallback : Memory) : OracleComp (SharedSequence.Shared Cfg Input Digest) (Packet F Memory b c r) :=
  if enabled then do
    let memory ← before
    packet ctx <$> SharedContinuation.program
      (PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample nodes ((1+r)+c))) (receive memory)
  else pure (disabled fallback)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Every supported accepted packet carries the computed arithmetic flag. -/
theorem program_checked (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F) (ctx : Context F b c r)
    (enabled : Bool) (before : OracleComp (SharedSequence.Shared Cfg Input Digest) Memory)
    (receive : Memory → Query F b ((1+r)+c) → OracleComp (SharedSequence.Shared Cfg Input Digest) (Values F b × Memory))
    (fallback : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Packet F Memory b c r × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes ctx enabled before receive fallback)).run state))
    (accepted : outcome.1.accepted = true) : check ctx outcome.1.query outcome.1.values = true := by
  cases enabled with
  | false =>
    simp only [program,Bool.false_eq_true,ite_false,simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    subst outcome
    exact (Bool.false_ne_true accepted).elim
  | true =>
    rw [program,ite_eq_left rfl,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨prepared,_,received⟩ := supported
    rw [simulateQ_map,StateT.run_map,support_map,Set.mem_image] at received
    obtain ⟨result,_,same⟩ := received
    subst outcome
    exact accepted

variable [Fintype F]

/-- The prover can adapt values and schedule work after the common fresh query.
A false fixed-source family pays one compression rate for all seven equations. -/
theorem truthful_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F) (sources : Sources F b c r)
    (enabled : Bool) (before : OracleComp (SharedSequence.Shared Cfg Input Digest) Memory)
    (receive : Memory → Query F b ((1+r)+c) → OracleComp (SharedSequence.Shared Cfg Input Digest) (Values F b × Memory))
    (fallback : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : ¬FullHolds sources) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes (context sources) enabled before receive fallback)).run state}[Truthful sources outcome.1] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*b-1 : ℕ) : ENNReal)/Fintype.card F)^b))) := by
  cases enabled with
  | false => simp [program,disabled,Truthful,prEvent_norm]
  | true =>
    rw [program,ite_eq_left rfl,simulateQ_bind,StateT.run_bind]
    apply prEvent_bind_le_of_forall_le
    intro prepared
    rw [simulateQ_map,StateT.run_map,prEvent_map]
    have retained := SharedContinuation.earlier_event_le enc dummy shape
      (PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample nodes ((1+r)+c))) (receive prepared.1) prepared.2
      (FullCheck sources)
    have arithmetic := AccumulatorEndpointSoundness.fresh_full_bound nodes sources falseClaim
    have bound := retained.trans (by simpa only [PrivateSampling.run_probComp,prEvent_norm] using arithmetic)
    apply le_trans (prEvent_mono _ _ _ ?_) bound
    intro outcome truthful
    exact truthful_check sources outcome.1.1 outcome.1.2.1 truthful.2 truthful.1

end
end FormalProof4FHE.HasteBoots.PackedAccumulatorOracle
