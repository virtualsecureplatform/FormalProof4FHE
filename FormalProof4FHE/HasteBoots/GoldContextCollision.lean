module
public import FormalProof4FHE.HasteBoots.GoldContextInput
public import FormalProof4FHE.HasteBoots.NativeHashOracleBridge
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
@[expose] public section

/-! Equal observed Goldilocks contexts identify full parameter records outside
the existing shared hash bad event. No new random-oracle exception or charge
is introduced, and an unobserved context computation is not sufficient. -/
namespace FormalProof4FHE.HasteBoots.GoldContextCollision
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored description)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem context_run (parameters : Parameters Stored) (world : World) :
    (run (NativeBrakedownContext.context description.row parameters) world).run =
      (some (InputIndexedOracle.sha512 world (GoldContextInput.bytes parameters)),
        [Observation.hash (GoldContextInput.bytes parameters) (List.ofFn (InputIndexedOracle.sha512 world (GoldContextInput.bytes parameters)))]) :=
  NativeBrakedownContext.context_success description.row parameters _ (GoldContextInput.input_eq parameters) world

theorem observed (parameters : Parameters Stored) (world : World) (digest : Digest)
    (computed : (run (NativeBrakedownContext.context description.row parameters) world).run.1 = some digest)
    (history : List Observation)
    (contained : (run (NativeBrakedownContext.context description.row parameters) world).run.2.Sublist history) :
    Observation.hash (GoldContextInput.bytes parameters) (List.ofFn digest) ∈ history := by
  rw [context_run] at computed contained
  cases Option.some.inj computed
  exact contained.subset List.mem_cons_self

theorem parameters_eq (left right : Parameters Stored) (world : World) (digest : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left) world).run.1 = some digest)
    (rightComputed : (run (NativeBrakedownContext.context description.row right) world).run.1 = some digest)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (leftObserved : (run (NativeBrakedownContext.context description.row left) world).run.2.Sublist history)
    (rightObserved : (run (NativeBrakedownContext.context description.row right) world).run.2.Sublist history)
    (noCollision : ¬OracleComp.CacheHasCollision (JointHashCache.project history).cache) : left = right := by
  by_contra different
  have leftKnown := NativeHashOracleBridge.cache_known world history truthful _ digest (observed left world digest leftComputed history leftObserved)
  have rightKnown := NativeHashOracleBridge.cache_known world history truthful _ digest (observed right world digest rightComputed history rightObserved)
  apply noCollision
  exact ⟨GoldContextInput.bytes left,GoldContextInput.bytes right,digest,digest,
    (fun same => different (GoldContextInput.bytes_injective same)),leftKnown,rightKnown,HEq.rfl⟩

theorem parameters_eq_of_no_bad (left right : Parameters Stored) (world : World) (digest : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left) world).run.1 = some digest)
    (rightComputed : (run (NativeBrakedownContext.context description.row right) world).run.1 = some digest)
    (dummy : Digest) (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (leftObserved : (run (NativeBrakedownContext.context description.row left) world).run.2.Sublist history)
    (rightObserved : (run (NativeBrakedownContext.context description.row right) world).run.2.Sublist history)
    (noBad : ¬NativeRootFamilyLifetime.Bad dummy history) : left = right := by
  apply parameters_eq left right world digest leftComputed rightComputed history truthful leftObserved rightObserved
  intro collision
  apply noBad
  apply Or.inr
  rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
  exact collision

theorem parameters_or_bad (left right : Parameters Stored) (world : World) (digest : Digest)
    (leftComputed : (run (NativeBrakedownContext.context description.row left) world).run.1 = some digest)
    (rightComputed : (run (NativeBrakedownContext.context description.row right) world).run.1 = some digest)
    (dummy : Digest) (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (leftObserved : (run (NativeBrakedownContext.context description.row left) world).run.2.Sublist history)
    (rightObserved : (run (NativeBrakedownContext.context description.row right) world).run.2.Sublist history) :
    left = right ∨ NativeRootFamilyLifetime.Bad dummy history := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy history
  · exact Or.inr bad
  · exact Or.inl (parameters_eq_of_no_bad left right world digest leftComputed rightComputed dummy history truthful leftObserved rightObserved bad)

end
end FormalProof4FHE.HasteBoots.GoldContextCollision
