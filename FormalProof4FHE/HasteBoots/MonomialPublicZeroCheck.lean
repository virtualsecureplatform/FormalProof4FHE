module
public import FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck
public import FormalProof4FHE.HasteBoots.PackedMonomialLayout
@[expose] public section

/-! The monomial terminal fixes its verifier public table and checks
input-evaluation times public monomial equals output-evaluation. Only the two
original private evaluation roots are committed and opened. -/
namespace FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening
noncomputable section

def arity : Bool → ℕ | false => 2 | true => 1

def indices : (term : Bool) → Fin (arity term) → Bool ⊕ Unit
  | false,index => if index.val = 0 then .inl false else .inr ()
  | true,_ => .inl true

def coefficient {F : Type} [Field F] : Bool → F | false => 1 | true => -1

theorem expression_eq {F : Type} [Field F] (values : Bool ⊕ Unit → F) :
    PackedSumcheckRound.expression arity coefficient indices values =
      values (.inl false)*values (.inr ())-values (.inl true) := by
  have productTerm : coefficient (F := F) false * (∏ index : Fin (arity false), values (indices false index)) =
      values (.inl false)*values (.inr ()) := by
    change (1 : F) * (∏ index : Fin 2, values (if index.val = 0 then .inl false else .inr ())) = _
    simp [Fin.prod_univ_two]
  have outputTerm : coefficient (F := F) true * (∏ index : Fin (arity true), values (indices true index)) = -values (.inl true) := by
    change (-1 : F) * (∏ _ : Fin 1, values (.inl true)) = _
    simp
  rw [PackedSumcheckRound.expression,Fintype.sum_bool,productTerm,outputTerm]
  ring

theorem vanishes_iff {F : Type} [Field F] {n b : ℕ}
    (privateTables : Bool → MatrixFold.Cube (n+1) → Fin b → F)
    (publicTable : MatrixFold.Cube (n+1) → Fin b → F) :
    PackedZeroCube.Vanishes arity coefficient indices (Sum.elim privateTables (fun _ : Unit => publicTable)) ↔
      ∀ cell lane, privateTables true cell lane = privateTables false cell lane * publicTable cell lane := by
  simp only [PackedZeroCube.Vanishes,expression_eq,Sum.elim_inl,Sum.elim_inr,sub_eq_zero,eq_comm]

variable {q lanes cells rows rounds : ℕ} [Fact q.Prime]

/-- The materialized native public plan is fixed before any query; active
rotations and padding use the already proved native address/half order. -/
def table (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) :
    MatrixFold.Cube ((cells+rows)+1) → Fin (2^lanes) → ZMod q :=
  fun cell => PackedMonomialLayout.word (rows := rows) psi rotations (FlatMatrixFold.index ((cells+rows)+1) cell).val

/-- A full query folds one fixed public source, independent of how it was
returned by the ZeroCheck protocol. -/
theorem fold_table (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(cells+lanes))))
    (query : PackedSumcheckSubclaim.Query (ZMod q) (2^lanes) ((cells+rows)+1)) :
    query.fold (table (rows := rows) psi rotations) = FlatMatrixFold.foldAll query.toList
      (fun position => PackedMonomialLayout.word (rows := rows) psi rotations position.val) :=
  SubclaimSourceLayout.fold_lookup query _

/-- The optimized native evaluator computes this same fixed-table fold after
splitting a complete query in coefficient/row/half order. No evaluator equality
or query-dependent public source is supplied as a security hypothesis. -/
theorem fold_eq_evaluate (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(cells+lanes))))
    (primitive : IsPrimitiveRoot psi (2^(cells+lanes+1)))
    (query : PackedSumcheckSubclaim.Query (ZMod q) (2^lanes) ((cells+rows)+1))
    (coefficientQuery rowQuery : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (half : MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes)))
    (coefficientLength : coefficientQuery.length = cells) (rowLength : rowQuery.length = rows)
    (ordered : query.toList = coefficientQuery++(rowQuery++[half])) :
    query.fold (table (rows := rows) psi rotations) =
      PublicMonomialEvaluation.evaluate psi lanes coefficientQuery rowQuery half
        (fun index => finCongr (congrArg (fun size => 2*(2^(size+lanes))) coefficientLength).symm (rotations index)) := by
  subst cells
  subst rows
  rw [fold_table,ordered]
  exact (PackedMonomialLayout.evaluate_source psi lanes coefficientQuery rowQuery half primitive rotations).symm

variable {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Input] [DecidableEq Digest]
  {front suffix m queries height : ℕ}

local notation "NativeScheme" => AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg Response Memory CommitMemory (2^lanes) (cells+rows) front suffix m queries height

/-- Fix the public plan, polynomial and two caller-owned private roots. Factory
commitment work and private memory remain; public factors have no commitments. -/
def configure (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (roots : Bool → Digest) (s : NativeScheme) : NativeScheme :=
  {s with
    encoding := enc
    factors := [false,true]
    arity := arity
    coefficient := coefficient
    indices := indices
    publicTables := fun _ _ => table (rows := rows) psi rotations
    commit := do
      let original ← s.commit
      pure (roots,original.2)}

def stage (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q) (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (roots : Bool → Digest) (s : NativeScheme) : NativeScheme :=
  AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (configure enc psi rotations roots s)

omit [DecidableEq Input] [DecidableEq Digest] in
theorem public_source (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q) (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (roots : Bool → Digest) (s : NativeScheme)
    (emission : (Bool → Digest) × CommitMemory) :
    (stage firstSmall roundSmall nodesEnough enc psi rotations roots s).publicTables emission () = table (rows := rows) psi rotations := rfl

omit [DecidableEq Input] in
/-- The original-owner ZeroCheck relation is precisely the monomial product
on the two private evaluation sources and the fixed native public plan. -/
theorem original_vanishes_iff
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (roots : Bool → Digest) (s : NativeScheme)
    (heights : Cfg → ℕ) (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (emission : (Bool → Digest) × CommitMemory) :
    PackedZeroCube.Vanishes
      (stage firstSmall roundSmall nodesEnough enc psi rotations roots s).arity
      (stage firstSmall roundSmall nodesEnough enc psi rotations roots s).coefficient
      (stage firstSmall roundSmall nodesEnough enc psi rotations roots s).indices
      (AmbientPublicZeroCheck.originalSources heights (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy capacity radius owner emission) ↔
    ∀ cell lane,
      AmbientPublicZeroCheck.originalPrivateSources heights (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy capacity radius owner true cell lane =
      AmbientPublicZeroCheck.originalPrivateSources heights (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy capacity radius owner false cell lane *
        table (rows := rows) psi rotations cell lane := by
  change PackedZeroCube.Vanishes arity coefficient indices
    (Sum.elim (AmbientPublicZeroCheck.originalPrivateSources heights
      (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy capacity radius owner)
      (fun _ : Unit => table (rows := rows) psi rotations)) ↔ _
  exact vanishes_iff _ _

variable [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))] [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (TestMatrix (ZMod q) (2^front) (2^lanes))] [SampleableType (Fin queries → Fin (2^height))]

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)] [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Both actual private roots are the enclosing monomial evaluation roots,
including executions whose later arithmetic or native opening work rejects. -/
theorem witness_roots (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q) (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (roots : Bool → Digest) (s : NativeScheme)
    (heights : Cfg → ℕ) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : AmbientPublicZeroCheck.Prefix heights (Private := Bool) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      AmbientPublicZeroCheck.RunResult heights (F := ZMod q) (Private := Bool) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := (2^lanes)) (n := (cells+rows)) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AmbientPublicZeroCheck.witness heights (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy initial)) :
    outcome.1.1.1 = roots := by
  simp only [AmbientPublicZeroCheck.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [stage,AuthenticatedPublicZeroCheck.nativeScheme,configure,simulateQ_bind,StateT.run_bind,
    simulateQ_pure,StateT.run_pure,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨original,_,same⟩ := firstSupported
  subst first
  rfl

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin (2^lanes)) → K)]

/-- The fixed monomial product and two original evaluation openings have a
derived native rate on the inherited state, outside its shared final exception.
Neither the public plan nor a message degree/security flag comes from the prover. -/
theorem original_safe_bound [NeZero m] (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1) (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (roots : Bool → Digest) (s : NativeScheme)
    (heights : Cfg → ℕ) (geometry : ∀ factor, heights (s.tag factor) = height)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (AmbientPublicZeroCheck.witness heights (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy initial)}[
      AmbientPublicZeroCheck.OriginalRisk heights (stage firstSmall roundSmall nodesEnough enc psi rotations roots s) dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) + ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := (2^lanes)) (queries := queries) s.domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := (2^lanes)) (queries := queries) s.domain radius) := by
  have complete : ∀ factor, factor ∈ (configure enc psi rotations roots s).factors := by intro factor; cases factor <;> simp [configure]
  have bounded : ∀ term, (configure enc psi rotations roots s).arity term ≤ 2 := by
    intro term
    cases term
    · exact Nat.le_refl 2
    · exact Nat.one_le_of_lt (by decide +kernel : 0 < 2)
  have bound := AmbientPublicZeroCheck.native_original_safe_bound q 2 firstSmall roundSmall nodesEnough heights
    (configure enc psi rotations roots s) geometry basis dummy complete enough capacity radius bounded small initial audited
  simpa only [stage,configure,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_add] using bound

end
end FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck
