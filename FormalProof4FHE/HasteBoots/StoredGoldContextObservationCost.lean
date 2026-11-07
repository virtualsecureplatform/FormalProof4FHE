module
public import FormalProof4FHE.HasteBoots.StoredGoldContextEncodingCost
public import FormalProof4FHE.HasteBoots.StoredMetadataCost
public import FormalProof4FHE.HasteBoots.JointHashCache
@[expose] public section

/-! Bind stored parameter bytes to a complete observed context-hash response.
Only actual hash observations can witness a context; SHAKE output is distinct.
All encoding, byte comparison and history traversal is charged. Truthfulness
and the existing shared-cache collision event are used only in semantic proofs,
not as executable certificates or extra independent failure events. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldContextObservationCost
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredGoldContextEncodingCost (Parameters)
open StoredMetadataCost (Root)


def matchesBytes (expected : Input) (context : Root) : Observation → Run Bool
  | .hash input output =>
    let sameInput := BytePrefixMatchCost.equal input expected
    if sameInput.value then
      let stored := StoredDigestView.fromVector context
      let sameOutput := BytePrefixMatchCost.equal output stored.value.val
      ⟨sameOutput.value,sameInput.cost+stored.cost+sameOutput.cost+5⟩
    else ⟨false,sameInput.cost+3⟩
  | _ => ⟨false,1⟩

theorem matchesBytes_value (expected : Input) (context : Root) (entry : Observation) :
    (matchesBytes expected context entry).value = decide (entry = .hash expected context.toList) := by
  cases entry with
  | start input => rfl
  | output input offset output => rfl
  | hash input output =>
    by_cases same : input = expected <;>
      simp [matchesBytes,BytePrefixMatchCost.equal_value,StoredDigestView.fromVector,same,Observation.hash.injEq]

theorem matchesBytes_cost (expected : Input) (context : Root) (entry : Observation) :
    (matchesBytes expected context entry).cost ≤ 6*expected.length+550 := by
  cases entry with
  | start input => simp only [matchesBytes]; omega
  | output input offset output => simp only [matchesBytes]; omega
  | hash input output =>
    have sameInput := BytePrefixMatchCost.equal_cost input expected
    have inputSize := Nat.min_le_right input.length expected.length
    have sameOutput := BytePrefixMatchCost.equal_cost output context.toList
    have outputSize := Nat.min_le_right output.length context.toList.length
    simp only [Vector.length_toList] at sameOutput outputSize
    simp only [matchesBytes]
    split
    · dsimp only [StoredDigestView.fromVector]; omega
    · dsimp only; omega

def scan (expected : Input) (context : Root) : List Observation → Run Bool
  | [] => ⟨false,1⟩
  | head::tail =>
    let matched := matchesBytes expected context head
    if matched.value then ⟨true,matched.cost+3⟩
    else
      let rest := scan expected context tail
      ⟨rest.value,matched.cost+rest.cost+4⟩

theorem scan_value (expected : Input) (context : Root) (history : List Observation) :
    (scan expected context history).value = decide (.hash expected context.toList ∈ history) := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head = .hash expected context.toList <;>
      simp only [scan,matchesBytes_value,same,decide_true,decide_false,ite_true,Bool.false_eq_true,
        ite_false,ih,List.mem_cons,eq_comm,true_or,false_or]

theorem scan_cost (expected : Input) (context : Root) (history : List Observation) :
    (scan expected context history).cost ≤ (6*expected.length+554)*history.length+1 := by
  induction history with
  | nil => simp [scan]
  | cons head tail ih =>
    have matched := matchesBytes_cost expected context head
    simp only [scan,List.length_cons]
    split <;> dsimp only <;> nlinarith

def verify (parameters : Parameters) (context : Root) (history : List Observation) : Run Bool :=
  let encoded := StoredGoldContextEncodingCost.input parameters
  let checked := scan encoded.value context history
  ⟨checked.value,encoded.cost+checked.cost+2⟩

theorem verify_value (parameters : Parameters) (context : Root) (history : List Observation) :
    (verify parameters context history).value =
      decide (.hash (StoredGoldContextEncodingCost.input parameters).value context.toList ∈ history) :=
  scan_value _ _ _

theorem verify_cost (parameters : Parameters) (context : Root) (history : List Observation) :
    (verify parameters context history).cost ≤
      (6*(parameters.code.modulus.val.length+StoredGoldContextEncodingCost.fixedBytes+
        NativeBrakedownContext.domain.length+126)+554)*history.length+
      9*parameters.code.modulus.val.length+6*StoredGoldContextEncodingCost.fixedBytes+
        3*NativeBrakedownContext.domain.length+1607 := by
  have encoded := StoredGoldContextEncodingCost.input_cost parameters
  have size := StoredGoldContextEncodingCost.input_size parameters
  have checked := scan_cost (StoredGoldContextEncodingCost.input parameters).value context history
  have scaled := Nat.mul_le_mul_right history.length (Nat.mul_le_mul_left 6 size)
  simp only [verify]
  nlinarith

def bound (parameters : Parameters) (history : List Observation) : ℕ :=
  (6*(parameters.code.modulus.val.length+StoredGoldContextEncodingCost.fixedBytes+
    NativeBrakedownContext.domain.length+126)+554)*history.length+
  9*parameters.code.modulus.val.length+6*StoredGoldContextEncodingCost.fixedBytes+
    3*NativeBrakedownContext.domain.length+1607

theorem verify_bound (parameters : Parameters) (context : Root) (history : List Observation) :
    (verify parameters context history).cost ≤ bound parameters history := verify_cost _ _ _

theorem verify_member (parameters : Parameters) (context : Root) (history : List Observation)
    (accepted : (verify parameters context history).value = true) :
    .hash (StoredGoldContextEncodingCost.input parameters).value context.toList ∈ history := by
  rw [verify_value] at accepted
  exact of_decide_eq_true accepted

theorem verify_digest (parameters : Parameters) (context : Root) (history : List Observation) (world : World)
    (truthful : ObservationReplay.Agrees world history)
    (accepted : (verify parameters context history).value = true) :
    context.get = InputIndexedOracle.sha512 world (StoredGoldContextEncodingCost.input parameters).value := by
  have matched := truthful _ (verify_member parameters context history accepted)
  change List.ofFn (InputIndexedOracle.sha512 world (StoredGoldContextEncodingCost.input parameters).value) = context.toList at matched
  apply Eq.symm
  apply List.ofFn_injective
  exact matched.trans (FixedByteReadCost.ofFn_get context).symm

theorem verify_context_program (parameters : Parameters) (context : Root) (history : List Observation) (world : World)
    (truthful : ObservationReplay.Agrees world history)
    (accepted : (verify parameters context history).value = true) :
    (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run =
      (some context.get,[.hash (StoredGoldContextEncodingCost.input parameters).value context.toList]) := by
  rw [NativeBrakedownContext.context_success _ _ _ (StoredGoldContextEncodingCost.input_value parameters).symm world,
    ← verify_digest parameters context history world truthful accepted,FixedByteReadCost.ofFn_get]

theorem verify_native_complete (parameters : Parameters) (context : Root) (history : List Observation) (world : World)
    (returned : (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.1 = some context.get)
    (included : (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row parameters) world).run.2.Sublist history) :
    (verify parameters context history).value = true := by
  have program := NativeBrakedownContext.context_success NativeGoldBlockCode.description.row parameters
    (StoredGoldContextEncodingCost.input parameters).value (StoredGoldContextEncodingCost.input_value parameters).symm world
  rw [program] at returned included
  have same := Option.some.inj returned
  rw [same,FixedByteReadCost.ofFn_get] at included
  rw [verify_value]
  exact decide_eq_true (included.subset (List.mem_singleton_self _))

noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem verify_cached (parameters : Parameters) (context : Root) (history : List Observation) (world : World)
    (truthful : ObservationReplay.Agrees world history)
    (accepted : (verify parameters context history).value = true) :
    (JointHashCache.project history).cache (StoredGoldContextEncodingCost.input parameters).value = some context.get := by
  have coherent := (JointHashCache.project_valid world history truthful).1
  have agrees := (JointHashCache.project_valid world history truthful).2
  have observed := verify_member parameters context history accepted
  have present : (StoredGoldContextEncodingCost.input parameters).value ∈ (JointHashCache.project history).keys := by
    rw [JointHashCache.project_keys]
    exact List.mem_toFinset.mpr ((JointHashCache.mem_hashInputs _ _).mpr ⟨context.toList,observed⟩)
  obtain ⟨answer,known⟩ := (coherent.mem_keys_iff _).mp present
  have same := (agrees _ _ known).trans (verify_digest parameters context history world truthful accepted).symm
  rw [← same]
  exact known

theorem verified_parameters_eq (first last : Parameters) (context : Root) (history : List Observation) (world : World)
    (truthful : ObservationReplay.Agrees world history)
    (firstAccepted : (verify first context history).value = true)
    (lastAccepted : (verify last context history).value = true)
    (noCollision : ¬OracleComp.CacheHasCollision (JointHashCache.project history).cache) : first = last := by
  apply StoredGoldContextEncodingCost.input_injective
  by_contra different
  have firstKnown := verify_cached first context history world truthful firstAccepted
  have lastKnown := verify_cached last context history world truthful lastAccepted
  exact noCollision ⟨_,_,_,_,different,firstKnown,lastKnown,HEq.rfl⟩
end
end FormalProof4FHE.HasteBoots.StoredGoldContextObservationCost
