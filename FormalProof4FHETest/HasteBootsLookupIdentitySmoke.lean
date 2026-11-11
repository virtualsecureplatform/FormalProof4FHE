module
public import FormalProof4FHE.HasteBoots.NativeSharedLookupGuard
public import FormalProof4FHE.HasteBoots.NativeScalarBatchVerifier
import all FormalProof4FHE.HasteBoots.LookupIdentityProtocol
import all FormalProof4FHETest.HasteBootsLookupNativeTerminalSmoke
import all FormalProof4FHETest.HasteBootsLookupSumCausalSmoke

namespace FormalProof4FHE.HasteBoots.LookupIdentitySmoke
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldWire (goldExtensionValue)
open HasteBootsScalarFinishAncestrySmoke (usize message)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open ScalarExecutionRecoverySmoke (before decoded)
open LookupNativeTerminalSmoke (selection output produced inputs point)
open MatrixFold (Cube)
deriving instance DecidableEq for NativeSharedLookupGuard.Request
deriving instance DecidableEq for NativeScalarBatchVerifier.SubClaim
noncomputable section

def request : NativeSharedLookupStatement.Request := ⟨2,[],1,⟨[0,1],usize 0⟩⟩
def job : NativeSharedLookupStatement.Prepared := ⟨⟨usize 0,0,request⟩,output⟩
def statement : NativeScalarBatchWire.Statement :=
  ⟨⟨[LookupScalarGrammar.sumInfo (usize 2),LookupScalarGrammar.identityInfo (usize 2) request],by decide⟩,
    ⟨[NativeGoldLookup.zero,NativeGoldLookup.zero],by decide⟩⟩
def identityMessage : NativeScalarBatchWire.Message :=
  ⟨⟨List.replicate 5 NativeGoldLookup.zero,by decide⟩⟩
def identityCertificate : NativePrefixCodec.Vector NativeScalarBatchWire.Message := ⟨[identityMessage,identityMessage],by decide⟩
def proof : NativeScalarBatchPreflight.Proof := ⟨[LookupSumCausalSmoke.certificate,identityCertificate],by decide⟩
def execution := NativeScalarBatchVerifier.execute statement proof 9 (NativeScalarBatchVerifier.initial child statement proof) worldZero
def claims : List NativeScalarBatchVerifier.SubClaim := execution.1.state.expected.map (fun value => ⟨execution.1.state.point,value⟩)
theorem finished : execution.1.control = .finished claims := rfl

def eqPoint (_ : Fin 2) := NativeGoldLookup.one
def data : NativeSharedLookupGuard.Inputs :=
  ⟨[request.terminal],[NativeSharedLookupGuard.Job.fromProduced 0 output],[List.ofFn eqPoint],
    List.ofFn (fun i => List.ofFn (inputs i)),[NativeGoldLookup.zero]⟩
def guarded? := NativeSharedLookupGuard.guard data claims 0 4
theorem guardPresent : guarded?.isSome = true := by decide +kernel
def result := guarded?.get guardPresent
theorem guarded : NativeSharedLookupGuard.guard data claims 0 4 = some result := (Option.some_get guardPresent).symm
def checked := result.checked[0]'(by decide +kernel)

def view : LookupIdentityView.View 1 0 (usize 2) job claims result 0 where
  checked := checked
  checkedAt := List.getElem?_eq_getElem _
  ordinalEq := by decide +kernel
  requestEq := by decide +kernel
  inputs := inputs
  inputsEq := by decide +kernel
  point := point
  eqPoint := eqPoint
  pointEq := by decide +kernel
  eqPointEq := by decide +kernel
  shape := LookupNativeTerminalSmoke.shape
  dimension := rfl
  claimAt := by decide +kernel
  claimPoint := by decide +kernel
  producer := ⟨job.tag.job,selection⟩
  produced := produced
  shift := by decide
  enough := by decide
  terminal := by decide +kernel

def sources (_ : Fin 2) (_ : Cube 0) (_ : Fin 4) : NativeFields.Goldilocks := 0
def helpers (cell : Cube 2) : Fin 8 → NativeFields.Goldilocks :=
  PaddedExtension.encode (padding := 5) goldilocksBasis (ScalarSourceSmoke.jointTable () cell)

theorem initialTruth : ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity
    (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices 2
    (LookupIdentityCausalReduction.partialTables (helperPadding := 5) view sources helpers) [] = 1 := by
  have identity := ScalarLookupExpression.partial_initial (F := NativeFields.Goldilocks) (K := Goldilocks3) (n := 2) (columns := 2)
    (fun _ => (1 : Goldilocks3)) (goldExtensionValue job.output.r) (goldExtensionValue job.output.y)
    (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) (row := 0) rfl (sources column))
    (fun cell => PaddedExtension.decode (padding := 5) goldilocksBasis (helpers cell)) 0
  have sumValue : (∑ cell : Cube 2, PackedEqualityCube.weight (n := 2) (fun _ : Fin 2 => (1 : Goldilocks3)) cell *
      ReciprocalMask.residual (goldExtensionValue job.output.r)
        (ExtensionLookupIdentity.hashTable (goldExtensionValue job.output.y)
          (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) (row := 0) rfl (sources column)) cell)
        (PaddedExtension.decode (padding := 5) goldilocksBasis (helpers cell))
        (decide ((FlatMatrixFold.index 2 cell).val < 0))) = 1 := by
    change (∑ cell : Bool × Bool × Unit, PackedEqualityCube.weight (n := 2) (fun _ : Fin 2 => (1 : Goldilocks3)) cell *
      ReciprocalMask.residual (goldExtensionValue job.output.r)
        (ExtensionLookupIdentity.hashTable (goldExtensionValue job.output.y)
          (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) (row := 0) rfl (sources column)) cell)
        (PaddedExtension.decode (padding := 5) goldilocksBasis (helpers cell))
        (decide ((FlatMatrixFold.index 2 cell).val < 0))) = 1
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,Fintype.sum_unique]
    have rawR : job.output.r = NativeGoldLookup.one := by decide +kernel
    have rValue : goldExtensionValue job.output.r = 1 := (congrArg goldExtensionValue rawR).trans NativeGoldLookup.one_value
    simp [helpers,ScalarSourceSmoke.jointTable,ReciprocalMask.residual,rValue]
    have weight : PackedEqualityCube.weight (n := 2) (fun _ : Fin 2 => (1 : Goldilocks3)) (true,true,()) = 1 := by
      calc
        _ = PackedEqualityCube.weight (n := 1) (fun _ : Fin 1 => (1 : Goldilocks3)) (true,()) := by
          simpa only [ite_true,one_mul] using PackedEqualityCube.weight_succ (n := 1) (fun _ : Fin 2 => (1 : Goldilocks3)) true (true,())
        _ = PackedEqualityCube.weight (n := 0) (fun _ : Fin 0 => (1 : Goldilocks3)) () := by
          simpa only [ite_true,one_mul] using PackedEqualityCube.weight_succ (n := 0) (fun _ : Fin 1 => (1 : Goldilocks3)) true ()
        _ = 1 := PackedEqualityCube.weight_zero _ _
    exact (congrArg₂ (fun a b : Goldilocks3 => a*b) weight (PaddedExtension.decode_encode (padding := 5) goldilocksBasis (1 : Goldilocks3))).trans (one_mul 1)
  simp only [ScalarNativeSourceHealing.truth,List.map_nil,LookupIdentityCausalReduction.partialTables,view,eqPoint,
    NativeGoldLookup.one_value,job,request,usize,Nat.zero_mod]
  exact identity.trans sumValue

theorem initiallyFalse : ScalarChainHealing.value 1 statement.claims.val ≠
    some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices 2
      (LookupIdentityCausalReduction.partialTables (helperPadding := 5) view sources helpers) []) := by
  rw [initialTruth]
  change some (goldExtensionValue NativeGoldLookup.zero) ≠ some 1
  rw [NativeGoldLookup.zero_value]
  exact fun same => zero_ne_one (Option.some.inj same)

theorem domain : NativeScalarTranscriptExtension.RoundDomain proof := by
  intro round packet source
  obtain ⟨round,bounded⟩ := round
  cases round with
  | zero =>
    have same : (⟨usize 0,⟨[message,identityMessage],by decide⟩⟩ : NativeScalarBatchWire.RoundPacket) = packet := Option.some.inj source
    rw [← same]
    decide +kernel
  | succ round =>
    cases round with
    | zero =>
      have same : (⟨usize 1,⟨[message,identityMessage],by decide⟩⟩ : NativeScalarBatchWire.RoundPacket) = packet := Option.some.inj source
      rw [← same]
      decide +kernel
    | succ round =>
      change none = some packet at source
      contradiction


/-- Actual scalar completion and native identity acceptance force an original
causal event or a wrong opening, with helper width eight/source width four. -/
theorem event_or_wrong :
    ScalarFinishedSourceEvent.Event child statement proof 9 worldZero ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices 2
      (LookupIdentityCausalReduction.partialTables (helperPadding := 5) view sources helpers) 1 (LookupScalarGrammar.identityInfo (usize 2) request) ∨
      LookupIdentityCausalReduction.Wrong (helperPadding := 5) view sources helpers :=
  LookupIdentityCausalReduction.partial_event_or_wrong (helperPadding := 5) view child before statement proof decoded (by decide +kernel)
    domain 9 worldZero finished rfl (by decide +kernel) sources helpers initiallyFalse

open NativeSharedLookupStatement (Request)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupProofShape (Values)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeSharedLookupPrelude (Ready guardInputs)
open NativeSharedLookupGuard (Result)

theorem originalGeometry {count padding : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper (List.ofFn requests) = some geometry)
    (openingCount : ℕ) (values : Values)
    (shape : NativeSharedLookupProofShape.check registry (List.ofFn requests) geometry openingCount values = true)
    (width : geometry.geometry.2.val = 3+padding)
    (rootFits : values.roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (transcript : Transcript) (world : World)
    (ready : Ready geometry.geometry.1.val)
    (prepared : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests geometry.geometry.1 values.multiplicities
      values.roots rootFits w lookupFuel equalityFuel transcript) world).run.1 = some ready)
    (proof : NativeScalarBatchPreflight.Proof) (fuel : ℕ) (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute ready.statement proof fuel
      (NativeScalarBatchVerifier.initial ready.equality.transcript ready.statement proof) world).1.control = .finished claims)
    (sourceVars : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard (guardInputs requests ready values.sources values.helpers)
      claims sourceVars geometry.geometry.2.val = some result) (index : Fin ready.jobs.length) :
    ∃ view : LookupIdentityView.View padding sourceVars geometry.geometry.1 (ready.jobs.get index) claims result index.val,
      geometry.geometry.1.val = NativeScalarQueryShape.laneBits (3+padding)+sourceVars ∧
      List.ofFn (fun i => List.ofFn (view.inputs i)) = view.checked.values ∧
      List.Forall₂ (fun slot value => values.sources[slot]? = some value)
        (ready.jobs.get index).tag.request.terminal.sourceSlots view.checked.values ∧
      ∃ draw, ready.machine.draws[index.val]? = some draw ∧ NativeGoldLookupEquality.DrawEvidence draw (List.ofFn view.eqPoint) := by
  obtain ⟨view,_,_,related,draw⟩ := LookupIdentityView.recover fits requests registry helper geometry preflight openingCount values shape width
    rootFits w lookupFuel equalityFuel transcript world ready prepared proof fuel claims finished sourceVars result passed index
  exact ⟨view,view.dimension,view.inputsEq,related,draw⟩

end
end FormalProof4FHE.HasteBoots.LookupIdentitySmoke
