module

public import FormalProof4FHE.HasteBoots.NativeExtensionRequest
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

/-!
# Typed scalar/vector request adapters and resumable scalar starts

`transcript.rs::classical_extension` binds `typed request kind` before the
raw extension request. Scalar starts expose the native reader before its
first candidate; driving that reader reproduces the scalar adapter exactly.
Total coordinate assembly is used only with proved complete canonical
lists on reachable completed draws. Rust representation refinement remains
separate; no private-coin distribution is asserted here.
-/

namespace FormalProof4FHE.HasteBoots.TypedFieldRequest

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (Program bind run)

inductive Kind where
  | scalar
  | vector
  deriving DecidableEq

def kindBytes : Kind → Input
  | .scalar => utf8 "scalar"
  | .vector => utf8 "vector"

def prepare (transcript : Transcript) (kind : Kind) : Transcript :=
  NativeTranscript.appendBytes transcript (utf8 "typed request kind") (kindBytes kind)

def extension (p degree w fuel : ℕ) (transcript : Transcript) (kind : Kind) (label : Input) (count : ℕ) :
    Program NativeFieldVector.Status :=
  NativeExtensionRequest.request p degree w fuel (prepare transcript kind) label count

def scalarPhase (p degree w : ℕ) (transcript : Transcript) (label : Input) : NativeTranscript.FieldPhase :=
  (NativeTranscript.beginField (NativeExtensionRequest.prepare (prepare transcript .scalar) degree w) label p degree).run.1

def beginScalar (p degree w : ℕ) (transcript : Transcript) (label : Input) : Program NativeFieldVector.State :=
  bind (NativeTranscriptProgram.beginField
    (NativeExtensionRequest.prepare (prepare transcript .scalar) degree w) label p degree)
    (fun phase => .pure (NativeFieldVector.initial phase degree))

def beginExecute (p degree w : ℕ) (transcript : Transcript) (label : Input) :
    NativeFieldVector.State × List Observation :=
  let phase := scalarPhase p degree w transcript label
  (NativeFieldVector.initial phase degree, [.start phase.pending.input])

theorem run_beginScalar (p degree w : ℕ) (world : World) (transcript : Transcript) (label : Input) :
    (run (beginScalar p degree w transcript label) world).run = beginExecute p degree w transcript label := rfl

theorem drive_scalar (p degree w fuel : ℕ) (world : World) (transcript : Transcript) (label : Input) :
    (run (bind (beginScalar p degree w transcript label) (NativeFieldVector.drive p fuel)) world).run =
      (run (extension p degree w fuel transcript .scalar label 1) world).run := by
  simp only [extension, NativeExtensionRequest.request, one_mul, NativeFieldVector.run_request,
    OracleProgram.run_bind, ObservationReplay.run_bind, run_beginScalar, NativeFieldVector.run_drive]
  rfl

def FieldValid (p degree : ℕ) (state : NativeFieldVector.State) : Prop :=
  state.remaining + state.values.length = degree ∧ NativeFieldVector.ValuesValid p state

theorem begin_valid (p degree w : ℕ) (transcript : Transcript) (label : Input) :
    FieldValid p degree (beginExecute p degree w transcript label).1 := by
  simp [FieldValid, beginExecute, NativeFieldVector.initial, NativeFieldVector.ValuesValid]

theorem drive_valid (p degree fuel : ℕ) (world : World) (state : NativeFieldVector.State)
    (valid : FieldValid p degree state) :
    FieldValid p degree (NativeFieldVector.stateOf (NativeFieldVector.driveExecute p fuel state world).1) := by
  simp only [NativeFieldVector.driveExecute, NativeFieldVector.finish_state]
  exact ⟨(NativeFieldVector.count_invariant p fuel state world).trans valid.1,
    NativeFieldVector.values_valid p fuel state world valid.2⟩

theorem drive_finished_length (p degree fuel : ℕ) (world : World) (state completed : NativeFieldVector.State)
    (transcript : Transcript) (valid : FieldValid p degree state)
    (finished : (NativeFieldVector.driveExecute p fuel state world).1 = .finished completed transcript) :
    completed.values.length = degree ∧ NativeFieldVector.ValuesValid p completed := by
  have total := drive_valid p degree fuel world state valid
  have done := NativeFieldVector.finish_status world (NativeFieldVector.execute p fuel state world).1
  change NativeFieldVector.StatusValid (NativeFieldVector.driveExecute p fuel state world).1 at done
  rw [finished] at total done
  change completed.remaining = 0 at done
  change completed.remaining + completed.values.length = degree ∧ NativeFieldVector.ValuesValid p completed at total
  exact ⟨by omega, total.2⟩

/-- Every active scalar step first performs the native candidate read,
including on candidates later rejected or followed by a receipt. -/
theorem drive_read_head (p : ℕ) (world : World) (state : NativeFieldVector.State) (pending : state.remaining ≠ 0) :
    (NativeFieldVector.driveExecute p 1 state world).2.head? =
      some (.output state.phase.pending.input state.phase.consumed.length
        (InputIndexedOracle.bytes world state.phase.pending.input state.phase.consumed.length
          (CanonicalByteSampler.byteCount p))) := by
  simp only [NativeFieldVector.driveExecute, NativeFieldVector.execute, pending, ite_false,
    CanonicalTranscriptSampler.executePrefix, NativeTranscript.drawField, WriterT.run_mk]
  by_cases good : CanonicalTranscriptSampler.candidate p
      (InputIndexedOracle.bytes world state.phase.pending.input state.phase.consumed.length
        (CanonicalByteSampler.byteCount p)) < p
  · simp only [good, ite_true]
    rfl
  · simp only [good, ite_false]
    rfl

noncomputable def scalarValue {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (values : List ℕ) : K :=
  basis.equivFun.symm (fun i => ((values[i.val]?.getD 0 : ℕ) : ZMod p))

/-- On completed requests no default getter or modular reduction is used. -/
theorem scalar_coordinate {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (values : List ℕ)
    (length : values.length = degree) (valid : ∀ value ∈ values, value < p) (i : Fin degree) :
    (basis.equivFun (scalarValue basis values) i).val = values[i.val]'(by omega) := by
  simp only [scalarValue, LinearEquiv.apply_symm_apply]
  rw [List.getElem?_eq_getElem (by omega : i.val < values.length)]
  exact ZMod.val_natCast_of_lt (valid _ (List.getElem_mem (by omega)))

theorem scalarValue_singleton (p : ℕ) (values : List ℕ) :
    scalarValue (Module.Basis.singleton (Fin 1) (ZMod p)) values = ((values[0]?.getD 0 : ℕ) : ZMod p) := by
  apply (Module.Basis.singleton (Fin 1) (ZMod p)).equivFun.injective
  funext i
  rw [Subsingleton.elim i 0]
  simp only [scalarValue, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply,
    Module.Basis.singleton_repr]
  rfl

end FormalProof4FHE.HasteBoots.TypedFieldRequest
