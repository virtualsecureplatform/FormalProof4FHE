module

public import FormalProof4FHE.HasteBoots.NTTButterfly
public import FormalProof4FHE.HasteBoots.AuthenticatedNTT

@[expose] public section

/-!
# Packed negacyclic NTT in native coefficient/lane and output order

A packed polynomial position is coefficient-block-major and lane-minor.
Flattening preserves address lane+b*block. The exact-arithmetic butterfly
transform equals a concrete public linear map at odd bit-reversed root powers.
Replacing the abstract authenticated NTT's transform with this map connects
its false-source relation to the butterfly algorithm, rather than assuming
the algorithm's correctness. Primitive-root validation for native retained
roots and optimized integer-kernel/Rust refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.PackedNTT

noncomputable section

variable {F : Type} [Field F] {b c n : ℕ}

/-- Polynomial size is independent of PCS code-block width. -/
def address (length : 2 ^ c * b = 2 ^ n) : NTTCompression.Position c b ≃ Fin (2 ^ n) :=
  (Equiv.prodCongr (FlatMatrixFold.index c) (Equiv.refl (Fin b))).trans
    (finProdFinEquiv.trans (finCongr length))

theorem address_val (length : 2 ^ c * b = 2 ^ n) (cell : MatrixFold.Cube c) (lane : Fin b) :
    (address length (cell, lane)).val = lane.val + b * (FlatMatrixFold.index c cell).val := rfl

def flatten (length : 2 ^ c * b = 2 ^ n) (coefficients : NTTCompression.Position c b → F) : Fin (2 ^ n) → F :=
  fun index => coefficients ((address length).symm index)

def unflatten (length : 2 ^ c * b = 2 ^ n) (coefficients : Fin (2 ^ n) → F) : NTTCompression.Position c b → F :=
  fun position => coefficients (address length position)

omit [Field F] in
theorem unflatten_flatten (length : 2 ^ c * b = 2 ^ n) (coefficients : NTTCompression.Position c b → F) :
    unflatten length (flatten length coefficients) = coefficients := by
  funext position
  simp only [flatten, unflatten, Equiv.symm_apply_apply]

omit [Field F] in
theorem flatten_unflatten (length : 2 ^ c * b = 2 ^ n) (coefficients : Fin (2 ^ n) → F) :
    flatten length (unflatten length coefficients) = coefficients := by
  funext index
  simp only [flatten, unflatten, Equiv.apply_symm_apply]

/-- Native-order exact butterflies on one packed polynomial. -/
def butterfly (length : 2 ^ c * b = 2 ^ n) (psi : F) (coefficients : NTTCompression.Position c b → F) :
    NTTCompression.Position c b → F :=
  unflatten length (NTTButterfly.flatTransform n psi (psi ^ 2) (flatten length coefficients))

/-- The public linear map fixes both coefficient packing and output order. -/
def evaluation (length : 2 ^ c * b = 2 ^ n) (psi : F) :
    (NTTCompression.Position c b → F) →ₗ[F] (NTTCompression.Position c b → F) where
  toFun coefficients := unflatten length (NTTRowCheck.evaluation (NTTButterfly.nodes n psi) (flatten length coefficients))
  map_add' first second := by
    funext position
    simp [unflatten, flatten, NTTRowCheck.evaluation, add_mul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    funext position
    simp [unflatten, flatten, NTTRowCheck.evaluation, Finset.mul_sum, mul_assoc]

/-- Algorithm-to-linear-map equality is proved, never supplied by the prover. -/
theorem butterfly_evaluation (length : 2 ^ c * b = 2 ^ n) (psi : F)
    (root : IsPrimitiveRoot psi (2 ^ (n + 1))) (coefficients : NTTCompression.Position c b → F) :
    butterfly length psi coefficients = evaluation length psi coefficients := by
  unfold butterfly
  rw [NTTButterfly.negacyclic_evaluation n psi root]
  rfl

variable [DecidableEq F] {k : ℕ}

/-- Executes butterflies; its linearity follows from the evaluation theorem. -/
def butterflyLinear (length : 2 ^ c * b = 2 ^ n) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1))) :
    (NTTCompression.Position c b → F) →ₗ[F] (NTTCompression.Position c b → F) where
  toFun := butterfly length psi
  map_add' first second := by simp only [butterfly_evaluation length psi root, map_add]
  map_smul' scalar coefficients := by simp only [butterfly_evaluation length psi root, map_smul, RingHom.id_apply]

/-- Literal equality checking of all proposed coefficient/evaluation pairs. -/
def check (length : 2 ^ c * b = 2 ^ n) (psi : F)
    (coefficients evaluations : Fin k → NTTCompression.Position c b → F) : Bool :=
  (List.ofFn fun repetition => decide (butterfly length psi (coefficients repetition) = evaluations repetition)).all id

theorem check_evaluation (length : 2 ^ c * b = 2 ^ n) (psi : F)
    (root : IsPrimitiveRoot psi (2 ^ (n + 1))) (coefficients evaluations : Fin k → NTTCompression.Position c b → F) :
    check length psi coefficients evaluations = NTTRowCheck.check (evaluation length psi) coefficients evaluations := by
  simp only [check, NTTRowCheck.check, butterfly_evaluation length psi root]

variable {r : ℕ}

def Relation (length : 2 ^ c * b = 2 ^ n) (psi : F)
    (coefficients evaluations : MatrixFold.Cube r → NTTCompression.Position c b → F) : Prop :=
  ∀ row, butterfly length psi (coefficients row) = evaluations row

omit [DecidableEq F] in
theorem relation_evaluation (length : 2 ^ c * b = 2 ^ n) (psi : F)
    (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (coefficients evaluations : MatrixFold.Cube r → NTTCompression.Position c b → F) :
    Relation length psi coefficients evaluations ↔ NTTRowCheck.Relation (evaluation length psi) coefficients evaluations := by
  simp only [Relation, NTTRowCheck.Relation, butterfly_evaluation length psi root]

variable {Input Digest Cfg Response Memory CommitMemory : Type} {front suffix m queries height : ℕ}

/-- Any abstract factory transform is replaced by the concrete public packed
evaluation map. Only the original two commitments are used. -/
def scheme (length : 2 ^ c * b = 2 ^ n) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height) :
    AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height :=
  { s with transform := butterflyLinear length psi root }

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

omit [DecidableEq Input] [SampleableType Digest] [SampleableType (Fin k → Fin r → F)]
  [SampleableType (Fin b → F)] [SampleableType (TestMatrix F (2 ^ front) b)]
  [SampleableType (Fin queries → Fin (2 ^ height))] in
/-- The frozen decoded sources are unchanged by choosing the concrete transform. -/
theorem sources_scheme (length : 2 ^ c * b = 2 ^ n) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
      (Cfg := Cfg) (height := height)) :
    AuthenticatedNTT.sources (scheme length psi root s) dummy capacity radius first =
      AuthenticatedNTT.sources s dummy capacity radius first := rfl

def FalseRelation (length : 2 ^ c * b = 2 ^ n) (psi : F)
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (first : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
      (Cfg := Cfg) (height := height)) : Prop :=
  ¬Relation length psi
    (NTTCompression.sourceRows c r (AuthenticatedNTT.sources s dummy capacity radius first false))
    (NTTCompression.sourceRows c r (AuthenticatedNTT.sources s dummy capacity radius first true))

variable {K : Type} [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

/-- From-empty authenticated soundness for the actual exact-arithmetic packed
butterflies in native coefficient and bit-reversed output order. The factory's
transform is ignored. No butterfly-correctness or terminal-truthfulness
certificate is assumed; the primitive-root and PCS parameter conditions are
explicit. Native retained-root validation and optimized Rust refinement remain. -/
theorem soundness_from_empty [NeZero m] [NeZero b] [SampleableType F] [SampleableType (Fin r → F)]
    (length : 2 ^ c * b = 2 ^ n) (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (s : AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (AuthenticatedNTT.witness (scheme length psi root s) dummy)}[
      FalseRelation length psi s dummy capacity radius outcome.1 ∧ AuthenticatedNTT.accepted outcome.2.1 = true] ≤
      ((((r : ENNReal) / Fintype.card F) ^ k) +
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) +
        (JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius +
          JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius)) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedNTT.program (scheme length psi root s))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have bound := AuthenticatedNTT.soundness_from_empty (scheme length psi root s) basis dummy enough capacity radius small
  apply le_trans (prEvent_mono _ _ _ ?_) bound
  intro outcome event
  exact event

end

end FormalProof4FHE.HasteBoots.PackedNTT
