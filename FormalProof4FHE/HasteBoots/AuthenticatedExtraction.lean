module
public import FormalProof4FHE.HasteBoots.AuthenticatedPublicZeroCheck
public import FormalProof4FHE.HasteBoots.KeySwitchExtraction
public import FormalProof4FHE.HasteBoots.KeySwitchExtractionSoundness
@[expose] public section

/-! The extraction stage commits and opens only the signed increment.
The mask and target are fixed verifier tables from the pre-query emission.
The bound uses one private PCS error and one hash charge for the complete
stopped execution, not three authenticated factor commitments. -/
namespace FormalProof4FHE.HasteBoots.AuthenticatedExtraction
open OracleSpec OracleComp BinaryTree Matrix
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
noncomputable section

/-- Original factor slots: increment, mask, target. -/
def factor : PBSHadamard.Factor 1 → Sum Unit Bool
  | .inl (_,false) => .inl ()
  | .inl (_,true) => .inr false
  | .inr _ => .inr true

theorem factor_bijective : Function.Bijective factor := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide +kernel

def indices (term : PBSHadamard.Term 1) (position : Fin (PBSHadamard.arity term)) : Sum Unit Bool :=
  factor (PBSHadamard.indices term position)

theorem expression {F : Type} [Field F] (values : Sum Unit Bool → F) :
    PackedSumcheckRound.expression PBSHadamard.arity PBSHadamard.coefficient indices values =
      values (.inl ()) * values (.inr false)-values (.inr true) := by
  calc
    _ = PackedSumcheckRound.expression PBSHadamard.arity PBSHadamard.coefficient PBSHadamard.indices (fun role => values (factor role)) := rfl
    _ = _ := by simpa only [Fin.sum_univ_one,factor] using PBSHadamard.expression (fun role => values (factor role))

variable {q c lanes dimension : ℕ} [Fact q.Prime]

def publicTables (positive : 0 < dimension) (acc : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : NativePublic.Ciphertext q dimension) : Bool → MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q :=
  fun target => if target then KeySwitchExtraction.pack (KeySwitchExtraction.target positive acc output)
    else KeySwitchExtraction.pack (KeySwitchExtraction.mask q (2^(c+lanes)) dimension)

def Relation (positive : 0 < dimension) (acc : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : NativePublic.Ciphertext q dimension) (increment : MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q) : Prop :=
  ∀ cell lane, publicTables positive acc output true cell lane = increment cell lane * publicTables positive acc output false cell lane

theorem vanishes_iff (positive : 0 < dimension) (acc : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : NativePublic.Ciphertext q dimension) (privateTables : Unit → MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q) :
    PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient indices
      (Sum.elim privateTables (publicTables positive acc output)) ↔ Relation positive acc output (privateTables ()) := by
  simp only [PackedZeroCube.Vanishes,expression,sub_eq_zero,Relation,Sum.elim_inl,Sum.elim_inr]
  exact forall_congr' (fun _ => forall_congr' (fun _ => eq_comm))

theorem extraction_of_relation (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc increment : NativeBlindRotation.Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension)
    (relation : Relation positive acc output (KeySwitchExtraction.pack (c := c) (lanes := lanes) increment)) :
    CanonicalKeySwitch.Extraction shape acc increment output := by
  apply KeySwitchExtraction.extraction_of_relation shape positive acc increment output
  intro cell lane
  simpa only [KeySwitchExtraction.tables,Fin.sum_univ_one,publicTables,Bool.true_eq,ite_true,
    Bool.false_eq_true,ite_false] using relation cell lane

variable {FirstMessage Message Input Digest Cfg Response Memory CommitMemory : Type}
  {front suffix m queries height : ℕ}

/-- Trusted native shape and public factors override the factory data. The
endpoint/output may be chosen adaptively before the actual ZeroCheck queries. -/
def stage (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (s : AuthenticatedPublicZeroCheck.Scheme (ZMod q) Unit Bool (PBSHadamard.Term 1) FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory (2^lanes) c front suffix m queries height) :=
  { s with
    arity := PBSHadamard.arity
    coefficient := PBSHadamard.coefficient
    indices := indices
    factors := [()]
    publicTables := fun emission => publicTables positive (acc emission) (output emission) }

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [DecidableEq Input] [DecidableEq Digest] [Fintype Digest] [SampleableType Digest]
  [SampleableType (ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (Fin c → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType ((Fin (2^front) × Fin (2^lanes)) → K)]

/-- Accepted false extraction-source relation: three ZeroCheck arithmetic
terms, ONE private PCS error, and one hash charge on the complete actual run.
No authenticated response or three-public-opening premise is assumed. -/
theorem native_soundness_from_empty [NeZero m]
    (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (s : AuthenticatedPublicZeroCheck.Scheme (ZMod q) Unit Bool (PBSHadamard.Term 1)
      (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q)
      (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
      Input Digest Cfg Response Memory CommitMemory (2^lanes) c front suffix m queries height)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m :
        Set (Fin (2^height) → K)) : ℚ≥0)/3) :
    Pr{let outcome ← (AuthenticatedPublicZeroCheck.witness
      (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s)) dummy)}[
      ¬Relation positive (acc outcome.1.1) (output outcome.1.1)
        (AuthenticatedPublicZeroCheck.privateSources s dummy capacity radius outcome.1 ()) ∧
      AuthenticatedPublicZeroCheck.accepted outcome.2.1 = true] ≤
      (KeySwitchExtractionSoundness.error q c (2^lanes) +
        JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) s.domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) s.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (AuthenticatedPublicZeroCheck.program (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s)))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  have complete : ∀ factor, factor ∈ (stage positive acc output s).factors := by
    intro factor
    cases factor
    simp [stage]
  have bound := AuthenticatedPublicZeroCheck.native_soundness_from_empty q 2 firstSmall roundSmall nodesEnough
    (stage positive acc output s) basis dummy complete enough capacity radius PBSHadamard.degree_bound small
  have semantic (first : AuthenticatedPublicZeroCheck.Prefix (Private := Unit) (Digest := Digest)
      (CommitMemory := CommitMemory) (Input := Input) (Cfg := Cfg) (height := height)) :
      PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient indices
        (AuthenticatedPublicZeroCheck.sources (stage positive acc output s) dummy capacity radius first) ↔
      Relation positive (acc first.1) (output first.1)
        (AuthenticatedPublicZeroCheck.privateSources s dummy capacity radius first ()) :=
    vanishes_iff positive (acc first.1) (output first.1) (AuthenticatedPublicZeroCheck.privateSources s dummy capacity radius first)
  change Pr{let outcome ← (AuthenticatedPublicZeroCheck.witness
      (AuthenticatedPublicZeroCheck.nativeScheme q 2 firstSmall roundSmall nodesEnough (stage positive acc output s)) dummy)}[
      ¬PackedZeroCube.Vanishes PBSHadamard.arity PBSHadamard.coefficient indices
        (AuthenticatedPublicZeroCheck.sources (stage positive acc output s) dummy capacity radius outcome.1) ∧
      AuthenticatedPublicZeroCheck.accepted outcome.2.1 = true] ≤ _ at bound
  simp only [semantic] at bound
  simpa only [stage,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    KeySwitchExtractionSoundness.error,ZMod.card] using bound

end
end FormalProof4FHE.HasteBoots.AuthenticatedExtraction
