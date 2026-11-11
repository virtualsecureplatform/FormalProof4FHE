module
public import FormalProof4FHE.HasteBoots.RootSafeExtension
public import FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension
import all Init.Data.String.Defs
@[expose] public section

/-! Equality-point sampling never appends a helper-roots frame after the
actual binder. The successful prelude supplies that exact bound origin. -/
namespace FormalProof4FHE.HasteBoots.RootSafeEquality
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open RootSafeExtension (Extends StateExtends StatusExtends)
open OracleProgram (run)
noncomputable section
variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def Equality (base : Transcript) (machine : NativeLookupEquality.Machine count K) : Prop :=
  Extends base machine.transcript ∧
    (∀ field, machine.active = some field → StateExtends base field) ∧
    ∀ draw ∈ machine.draws, StateExtends base draw.coefficients

omit [DecidableEq K] in
theorem equality_tick (base : Transcript) (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Equality base machine) : Equality base (NativeLookupEquality.tickExecute basis w machine world).1 := by
  obtain ⟨transcript,active,draws⟩ := valid
  by_cases complete : machine.remaining = 0
  · simpa only [Equality,NativeLookupEquality.tickExecute,complete,ite_true] using And.intro transcript (And.intro active draws)
  · cases field : machine.active with
    | none =>
      simp only [Equality,NativeLookupEquality.tickExecute,complete,ite_false,field]
      refine ⟨transcript,?_,draws⟩
      intro next same
      have selected : (TypedFieldVector.beginExecute p degree w count machine.transcript NativeLookupEquality.pointLabel).1 = next :=
        Option.some.inj same
      rw [← selected]
      exact StateExtends.trans transcript (RootSafeExtension.vector_begin p degree w count machine.transcript _ (by decide +kernel) descriptorFits)
    | some fieldState =>
      have driven := RootSafeExtension.drive_status base p 1 fieldState world (active fieldState field)
      cases status : (NativeFieldVector.driveExecute p 1 fieldState world).1 with
      | suspended next =>
        simp only [status,StatusExtends] at driven
        simp only [Equality,NativeLookupEquality.tickExecute,complete,ite_false,field,status]
        refine ⟨transcript,?_,draws⟩
        intro found same
        exact Option.some.inj same ▸ driven
      | finished next after =>
        simp only [status,StatusExtends] at driven
        simp only [Equality,NativeLookupEquality.tickExecute,complete,ite_false,field,status]
        refine ⟨driven.2,?_,?_⟩
        · intro found impossible
          contradiction
        · intro draw member
          simp only [List.mem_append,List.mem_singleton] at member
          rcases member with old | rfl
          · exact draws draw old
          · exact driven.1

omit [DecidableEq K] in
theorem equality_execute (base : Transcript) (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Equality base machine) : Equality base (NativeLookupEquality.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (equality_tick base basis w machine world descriptorFits valid)


omit [DecidableEq K] in
theorem equality_request (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (state : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Equality (NativeLookupEquality.bindRoots state roots fits)
      (run (NativeLookupEquality.request basis w count fuel state roots fits) world).run.1 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  exact equality_execute _ basis w fuel _ world descriptorFits
    ⟨Extends.refl _,by simp [NativeLookupEquality.initial],by simp [NativeLookupEquality.initial]⟩

theorem ready_origins {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (n : NativeUsizeMessage.Usize)
    (multiplicities : List (List NativeFieldRepresentation.GoldWord)) (roots : List NativeRootMessage.Digest)
    (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (state : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state) world).run.1 = some ready)
    (descriptorFits : (NativeExtensionDescriptor.descriptor 3 w).length < TranscriptFrame.lengthLimit) :
    ∃ child, NativeTranscriptExtension.Extends state child ∧
      Extends (NativeLookupEquality.bindRoots child roots rootFits) ready.equality.transcript ∧
      Equality (NativeLookupEquality.bindRoots child roots rootFits) ready.machine := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state world ready success
  obtain ⟨child,finished,machine,_⟩ := contract.lookup
  have lookupGood := NativeLookupTranscriptExtension.batch_execute state NativeExtensionFields.goldilocksBasis w lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) state) world descriptorFits (NativeLookupTranscriptExtension.batch_initial _ _)
  have earlier : NativeTranscriptExtension.Extends state child := by
    have current := lookupGood.1
    rw [finished] at current
    exact current
  have later := equality_request NativeExtensionFields.goldilocksBasis w n.val equalityFuel child roots rootFits world descriptorFits
  refine ⟨child,earlier,?_⟩
  rw [contract.child,machine]
  exact ⟨later.1,later⟩

end
end FormalProof4FHE.HasteBoots.RootSafeEquality
