module

public import FormalProof4FHE.HasteBoots.TypedFieldRequest

@[expose] public section

/-!
# Resumable typed extension-vector requests

The vector kind and descriptor precede the canonical coefficient reader.
One vector collects count*degree consecutive coefficients and emits exactly
the existing native receipt, including when count is zero. The same reader
is retained across analysis pauses. Canonical coordinate assembly is proved
on completed requests; word/representation refinement remains separate.
-/

namespace FormalProof4FHE.HasteBoots.TypedFieldVector

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript Observation)
open OracleProgram (Program bind run)

def phase (p degree w count : ℕ) (transcript : Transcript) (label : Input) : NativeTranscript.FieldPhase :=
  (NativeTranscript.beginField
    (NativeExtensionRequest.prepare (TypedFieldRequest.prepare transcript .vector) degree w)
      label p (count * degree)).run.1

def begin (p degree w count : ℕ) (transcript : Transcript) (label : Input) : Program NativeFieldVector.State :=
  bind (NativeTranscriptProgram.beginField
    (NativeExtensionRequest.prepare (TypedFieldRequest.prepare transcript .vector) degree w)
      label p (count * degree))
    (fun reader => .pure (NativeFieldVector.initial reader (count * degree)))

def beginExecute (p degree w count : ℕ) (transcript : Transcript) (label : Input) :
    NativeFieldVector.State × List Observation :=
  (NativeFieldVector.initial (phase p degree w count transcript label) (count * degree),
    [.start (phase p degree w count transcript label).pending.input])

theorem run_begin (p degree w count : ℕ) (world : World) (transcript : Transcript) (label : Input) :
    (run (begin p degree w count transcript label) world).run = beginExecute p degree w count transcript label := rfl

theorem drive_vector (p degree w count fuel : ℕ) (world : World) (transcript : Transcript) (label : Input) :
    (run (bind (begin p degree w count transcript label) (NativeFieldVector.drive p fuel)) world).run =
      (run (TypedFieldRequest.extension p degree w fuel transcript .vector label count) world).run := by
  simp only [TypedFieldRequest.extension, NativeExtensionRequest.request, NativeFieldVector.run_request,
    OracleProgram.run_bind, ObservationReplay.run_bind, run_begin, NativeFieldVector.run_drive]
  rfl

/-- Appending the fixed typed-vector prelude cannot erase or replace
any of the already absorbed transcript input. -/
theorem phase_input_injective (p degree w count : ℕ) (left right : Transcript) (label : Input)
    (same : (phase p degree w count left label).pending.input =
      (phase p degree w count right label).pending.input) : left.input = right.input := by
  simp only [phase, NativeTranscript.beginField, WriterT.run_mk, NativeExtensionRequest.prepare,
    TypedFieldRequest.prepare, NativeTranscript.appendBytes, NativeTranscript.absorb] at same
  exact List.append_cancel_right (List.append_cancel_right (List.append_cancel_right (List.append_cancel_right same)))

theorem begin_valid (p degree w count : ℕ) (transcript : Transcript) (label : Input) :
    TypedFieldRequest.FieldValid p (count * degree) (beginExecute p degree w count transcript label).1 := by
  exact ⟨by simp [beginExecute, NativeFieldVector.initial], by simp [beginExecute, NativeFieldVector.initial,
    NativeFieldVector.ValuesValid]⟩

noncomputable def value {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) (coefficients : List ℕ) : Fin count → K :=
  fun element => basis.equivFun.symm (fun coordinate =>
    ((coefficients[coordinate.val + degree * element.val]?.getD 0 : ℕ) : ZMod p))

/-- No default coefficient or modular reduction is used in a complete
canonical vector, and each element consumes its own consecutive block. -/
theorem value_coordinate {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) (coefficients : List ℕ)
    (length : coefficients.length = count * degree) (valid : ∀ coefficient ∈ coefficients, coefficient < p)
    (element : Fin count) (coordinate : Fin degree) :
    (basis.equivFun (value basis count coefficients element) coordinate).val =
      coefficients[coordinate.val + degree * element.val]'(by
        have bound := (finProdFinEquiv (element, coordinate)).isLt
        change coordinate.val + degree * element.val < count * degree at bound
        omega) := by
  simp only [value, LinearEquiv.apply_symm_apply]
  have bound : coordinate.val + degree * element.val < coefficients.length := by
    rw [length]
    exact (finProdFinEquiv (element, coordinate)).isLt
  rw [List.getElem?_eq_getElem bound]
  exact ZMod.val_natCast_of_lt (valid _ (List.getElem_mem bound))

theorem value_singleton (p count : ℕ) (coefficients : List ℕ) :
    value (Module.Basis.singleton (Fin 1) (ZMod p)) count coefficients =
      fun element => ((coefficients[element.val]?.getD 0 : ℕ) : ZMod p) := by
  funext element
  apply (Module.Basis.singleton (Fin 1) (ZMod p)).equivFun.injective
  funext coordinate
  rw [Subsingleton.elim coordinate 0]
  simp only [value, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply,
    Module.Basis.singleton_repr, Fin.val_zero, one_mul, zero_add]

end FormalProof4FHE.HasteBoots.TypedFieldVector
