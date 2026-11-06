module

public import FormalProof4FHE.HasteBoots.NativeTranscriptExtension
public import FormalProof4FHE.HasteBoots.NativeSharedLookupPrelude
public import FormalProof4FHE.HasteBoots.NativeForkAncestry
import all Init.Data.String.Defs

@[expose] public section

/-! Valid transcript extensions through native lookup and equality sampling.
Active readers, finished draw records, completed jobs and the final ready
transcript retain their ancestry across all finite analysis prefixes.
The actual Goldilocks launcher supplies its fork header without an input
lineage certificate. Domains remain explicit; freshness, receipt risk,
PCS authentication, attacker work and Rust refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends StateExtends StatusExtends)
open OracleProgram (run)
noncomputable section

variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K] [DecidableEq K]

def Selection (base : Transcript) (machine : NativeLookupChallenge.Machine K) : Prop :=
  (match machine.control with
  | .compression field => StateExtends base field
  | .reciprocal _ _ _ field => StateExtends base field
  | .finished _ _ _ _ transcript => Extends base transcript) ∧
  ∀ draw ∈ machine.draws, StateExtends base draw.coefficients

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem selection_initial (base state : Transcript) (before : Extends base state) (p degree w : ℕ)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Selection base (NativeLookupChallenge.initialExecute (K := K) p degree w state).1 := by
  exact ⟨StateExtends.trans before (NativeTranscriptExtension.scalar_begin p degree w state _ (by decide +kernel) descriptorFits),by simp [NativeLookupChallenge.initialExecute]⟩

theorem selection_tick (base : Transcript) (basis : Module.Basis (Fin degree) (ZMod p) K) (w width : ℕ)
    (rows : List (List (ZMod p))) (machine : NativeLookupChallenge.Machine K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Selection base machine) : Selection base (NativeLookupChallenge.tickExecute basis w width rows machine world).1 := by
  obtain ⟨current,draws⟩ := valid
  cases control : machine.control with
  | finished y r weights table transcript => simpa only [Selection,NativeLookupChallenge.tickExecute,control] using And.intro current draws
  | compression field =>
    simp only [control] at current
    have driven := NativeTranscriptExtension.drive_status base p 1 field world current
    cases status : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simp only [status,StatusExtends] at driven
      exact ⟨by simpa only [NativeLookupChallenge.tickExecute,control,status] using driven,by simpa only [NativeLookupChallenge.tickExecute,control,status] using draws⟩
    | finished next transcript =>
      simp only [status,StatusExtends] at driven
      simp only [Selection,NativeLookupChallenge.tickExecute,control,status]
      refine ⟨?_,?_⟩
      · exact StateExtends.trans driven.2 (NativeTranscriptExtension.scalar_begin p degree w transcript NativeLookupChallenge.reciprocalLabel (by decide +kernel) descriptorFits)
      · intro draw member
        simp only [List.mem_append,List.mem_singleton] at member
        rcases member with old | rfl
        · exact draws draw old
        · exact driven.1
  | reciprocal y weights table field =>
    simp only [control] at current
    have driven := NativeTranscriptExtension.drive_status base p 1 field world current
    cases status : (NativeFieldVector.driveExecute p 1 field world).1 with
    | suspended next =>
      simp only [status,StatusExtends] at driven
      exact ⟨by simpa only [NativeLookupChallenge.tickExecute,control,status] using driven,by simpa only [NativeLookupChallenge.tickExecute,control,status] using draws⟩
    | finished next transcript =>
      simp only [status,StatusExtends] at driven
      have added : ∀ draw ∈ machine.draws ++ [⟨TypedFieldRequest.scalarValue basis next.values,next⟩], StateExtends base draw.coefficients := by
        intro draw member
        rcases List.mem_append.mp member with old | added
        · exact draws draw old
        · obtain rfl := List.mem_singleton.mp added
          exact driven.1
      by_cases allowed : NativeLookupChallenge.allowed table (TypedFieldRequest.scalarValue basis next.values) = true
      · simpa only [Selection,NativeLookupChallenge.tickExecute,control,status,allowed,ite_true] using And.intro driven.2 added
      · have nextGood := StateExtends.trans driven.2 (NativeTranscriptExtension.scalar_begin p degree w transcript NativeLookupChallenge.reciprocalLabel (by decide +kernel) descriptorFits)
        simpa only [Selection,NativeLookupChallenge.tickExecute,control,status,allowed,Bool.false_eq_true,ite_false] using And.intro nextGood added

theorem selection_execute (base : Transcript) (basis : Module.Basis (Fin degree) (ZMod p) K) (w width fuel : ℕ)
    (rows : List (List (ZMod p))) (machine : NativeLookupChallenge.Machine K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Selection base machine) : Selection base (NativeLookupChallenge.execute basis w width rows fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (selection_tick base basis w width rows machine world descriptorFits valid)

def Batch (base : Transcript) (machine : NativeLookupBatch.Machine p K) : Prop :=
  (match machine.control with
  | .ready _ transcript | .finished transcript => Extends base transcript
  | .sampling _ _ selection => Selection base selection) ∧
  ∀ completed ∈ machine.completed, Selection base completed.selection

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem batch_initial (base : Transcript) (actions : List (NativeLookupBatch.Action p)) :
    Batch base (NativeLookupBatch.initial (K := K) actions base) := ⟨Extends.refl base,by simp [NativeLookupBatch.initial]⟩

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem after_sample (base : Transcript) (machine : NativeLookupBatch.Machine p K)
    (job : NativeLookupBatch.Job p) (todo : List (NativeLookupBatch.Action p)) (selection : NativeLookupChallenge.Machine K)
    (completed : ∀ record ∈ machine.completed, Selection base record.selection) (valid : Selection base selection) :
    Batch base (NativeLookupBatch.afterSample machine job todo selection) := by
  cases control : selection.control with
  | compression field => simpa only [Batch,NativeLookupBatch.afterSample,control] using And.intro valid completed
  | reciprocal y weights table field => simpa only [Batch,NativeLookupBatch.afterSample,control] using And.intro valid completed
  | finished y r weights table transcript =>
    simp only [Batch,NativeLookupBatch.afterSample,control]
    refine ⟨?_,?_⟩
    · simpa only [control] using valid.1
    · intro record member
      simp only [List.mem_append,List.mem_singleton] at member
      rcases member with old | rfl
      · exact completed record old
      · exact valid

theorem batch_tick (base : Transcript) (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Batch base machine) : Batch base (NativeLookupBatch.tickExecute basis w machine world).1 := by
  obtain ⟨current,completed⟩ := valid
  cases control : machine.control with
  | finished transcript => simpa only [Batch,NativeLookupBatch.tickExecute,control] using And.intro current completed
  | ready todo transcript =>
    simp only [control] at current
    cases todo with
    | nil => simpa only [Batch,NativeLookupBatch.tickExecute,control] using And.intro current completed
    | cons action todo =>
      cases action with
      | request ordinal =>
        simp only [Batch,NativeLookupBatch.tickExecute,control]
        refine ⟨?_,completed⟩
        exact current.trans (NativeTranscriptExtension.absorb transcript 1 NativeLookupBatch.requestLabel (NativeUsizeMessage.encode ordinal)
          ⟨by change NativeLookupBatch.requestLabel.length < _; decide +kernel,by
            change (NativeUsizeMessage.encode ordinal).length < _
            exact lt_of_le_of_lt (NativeUsizeMessage.encode_length ordinal) (by decide +kernel)⟩)
      | sample job =>
        simpa only [Batch,NativeLookupBatch.tickExecute,control] using And.intro (selection_initial base transcript current p degree w descriptorFits) completed
  | sampling job todo selection =>
    simp only [control] at current
    simpa only [NativeLookupBatch.tickExecute,control] using after_sample base machine job todo _ completed
      (selection_tick base basis w job.request.width job.request.rows selection world descriptorFits current)

theorem batch_execute (base : Transcript) (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupBatch.Machine p K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Batch base machine) : Batch base (NativeLookupBatch.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (batch_tick base basis w machine world descriptorFits valid)

def Equality (base : Transcript) (machine : NativeLookupEquality.Machine count K) : Prop :=
  Extends base machine.transcript ∧
    (∀ field, machine.active = some field → StateExtends base field) ∧
    ∀ draw ∈ machine.draws, StateExtends base draw.coefficients

theorem bind_roots (state : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64)
    (payloadFits : (NativeRootMessage.encode roots fits).length < TranscriptFrame.lengthLimit) :
    Extends state (NativeLookupEquality.bindRoots state roots fits) :=
  NativeTranscriptExtension.absorb state 1 NativeLookupEquality.rootsLabel _ ⟨by change NativeLookupEquality.rootsLabel.length < _; decide +kernel,payloadFits⟩

omit [Field K] [Algebra (ZMod p) K] [DecidableEq K] in
theorem equality_initial (base : Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64)
    (payloadFits : (NativeRootMessage.encode roots fits).length < TranscriptFrame.lengthLimit) :
    Equality base (NativeLookupEquality.initial (K := K) count base roots fits) :=
  ⟨bind_roots base roots fits payloadFits,by simp [NativeLookupEquality.initial],by simp [NativeLookupEquality.initial]⟩

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
      exact StateExtends.trans transcript (NativeTranscriptExtension.vector_begin p degree w count machine.transcript _ (by decide +kernel) descriptorFits)
    | some fieldState =>
      have driven := NativeTranscriptExtension.drive_status base p 1 fieldState world (active fieldState field)
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

/-- A successful native prelude extends both its original child and the exact root-bound equality state. -/
theorem ready_origins {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (n : NativeUsizeMessage.Usize)
    (multiplicities : List (List NativeFieldRepresentation.GoldWord)) (roots : List NativeRootMessage.Digest)
    (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (state : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state) world).run.1 = some ready)
    (descriptorFits : (NativeExtensionDescriptor.descriptor 3 w).length < TranscriptFrame.lengthLimit) :
    ∃ child, Extends state child ∧
      Extends (NativeLookupEquality.bindRoots child roots rootFits) ready.equality.transcript ∧
      Equality (NativeLookupEquality.bindRoots child roots rootFits) ready.machine := by
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state world ready success
  obtain ⟨child,finished,machine,_⟩ := contract.lookup
  have lookupGood := batch_execute state NativeExtensionFields.goldilocksBasis w lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) state) world descriptorFits (batch_initial _ _)
  have earlier : Extends state child := by
    have current := lookupGood.1
    rw [finished] at current
    exact current
  have later := equality_request NativeExtensionFields.goldilocksBasis w n.val equalityFuel child roots rootFits world descriptorFits
  refine ⟨child,earlier,?_⟩
  rw [contract.child,machine]
  exact ⟨later.1,later⟩

theorem ready_extends {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (n : NativeUsizeMessage.Usize)
    (multiplicities : List (List NativeFieldRepresentation.GoldWord)) (roots : List NativeRootMessage.Digest)
    (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (state : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state) world).run.1 = some ready)
    (descriptorFits : (NativeExtensionDescriptor.descriptor 3 w).length < TranscriptFrame.lengthLimit)
    (payloadFits : (NativeRootMessage.encode roots rootFits).length < TranscriptFrame.lengthLimit) :
    Extends state ready.equality.transcript := by
  obtain ⟨child,earlier,later⟩ := ready_origins fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state world ready success descriptorFits
  exact earlier.trans ((bind_roots child roots rootFits payloadFits).trans later.1)


theorem ready_draw_header {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (n : NativeUsizeMessage.Usize)
    (multiplicities : List (List NativeFieldRepresentation.GoldWord)) (roots : List NativeRootMessage.Digest)
    (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (state : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state) world).run.1 = some ready)
    (descriptorFits : (NativeExtensionDescriptor.descriptor 3 w).length < TranscriptFrame.lengthLimit)
    (payloadFits : (NativeRootMessage.encode roots rootFits).length < TranscriptFrame.lengthLimit)
    (profile : NativeRootMessage.Digest) (label context : Input) (seed : NativeRootMessage.Digest)
    (header : NativeChildSeedView.HasHeader state profile label context seed)
    (draw : NativeLookupEquality.Draw n.val NativeExtensionFields.Goldilocks3) (member : draw ∈ ready.machine.draws) :
    NativeChildSeedView.HasHeader draw.coefficients.phase.pending profile label context seed := by
  obtain ⟨child,earlier,_,readers⟩ := ready_origins fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state world ready success descriptorFits
  exact ((readers.2.2 draw member).1.header ((bind_roots child roots rootFits payloadFits).header (earlier.header header)))

/-- The actual gated native launcher retains its executed fork's seed through all lookup/equality samplers. -/
theorem launch_header {S B : Type} {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (policy : NativeSharedLookupValues.Policy)
    (registry : List NativeLookupBindGeometry.Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (state : NativeSharedLookupChild.State) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (NativeSharedLookupChild.launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.1 = some (state,ready))
    (payloadFits : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit) :
    NativeChildSeedView.HasHeader ready.equality.transcript parent.profile
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
      (InputIndexedOracle.block world (NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare parent proof.multiplicities)
        NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) 0 64) := by
  have launched := NativeSharedLookupChild.launch_spec fits requests policy registry geometry proof lookupFuel equalityFuel parent world state ready success
  have extension := ready_extends fits requests geometry.geometry.1 proof.values.multiplicities proof.values.roots proof.roots.property
    7 lookupFuel equalityFuel (NativeSharedLookupChild.startExecute world parent proof.multiplicities).1.2 world ready launched.2.2.2
    (by decide +kernel) payloadFits
  exact extension.header (NativeForkAncestry.start_header world parent proof.multiplicities)


theorem launch_draw_header {S B : Type} {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (policy : NativeSharedLookupValues.Policy)
    (registry : List NativeLookupBindGeometry.Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (state : NativeSharedLookupChild.State) (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val)
    (success : (run (NativeSharedLookupChild.launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.1 = some (state,ready))
    (payloadFits : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw geometry.geometry.1.val NativeExtensionFields.Goldilocks3) (member : draw ∈ ready.machine.draws) :
    NativeChildSeedView.HasHeader draw.coefficients.phase.pending parent.profile
      NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
      (InputIndexedOracle.block world (NativeForkAncestry.seedInput (NativeSharedLookupChild.prepare parent proof.multiplicities)
        NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext) 0 64) := by
  have launched := NativeSharedLookupChild.launch_spec fits requests policy registry geometry proof lookupFuel equalityFuel parent world state ready success
  exact ready_draw_header fits requests geometry.geometry.1 proof.values.multiplicities proof.values.roots proof.roots.property
    7 lookupFuel equalityFuel (NativeSharedLookupChild.startExecute world parent proof.multiplicities).1.2 world ready launched.2.2.2
    (by decide +kernel) payloadFits _ _ _ _ (NativeForkAncestry.start_header world parent proof.multiplicities) draw member

end
end FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension

