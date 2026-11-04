module

public import FormalProof4FHE.HasteBoots.NativeFieldVector
public import FormalProof4FHE.HasteBoots.NativeExtensionFields
public import FormalProof4FHE.HasteBoots.CanonicalExtensionSampler

@[expose] public section

/-!
# Typed assembly of completed native coefficient requests

Conversion preserves each accepted canonical integer exactly. Extension
assembly reads element*degree+coordinate, without further oracle operations.
The concrete bases are the native degree-3/6 power bases, not the PCS bases.
This is a mathematical conversion bridge; Rust lazy/Montgomery storage and
extension-basis descriptor bytes still require checked correspondence.
-/

namespace FormalProof4FHE.HasteBoots.NativeFieldAssembly

open NativeFieldVector

noncomputable section

def coefficients (p count : ℕ) (values : List ℕ) (length : values.length = count) :
    Fin count → ZMod p := fun i => (values[i.val]'(by omega) : ZMod p)

theorem coefficients_canonical (p count : ℕ) (values : List ℕ)
    (length : values.length = count) (valid : ∀ v ∈ values, v < p) (i : Fin count) :
    (coefficients p count values length i).val = values[i.val]'(by omega) := by
  apply ZMod.val_natCast_of_lt
  exact valid _ (List.getElem_mem (by omega))

def assemble {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ)
    (values : List ℕ) (length : values.length = count * degree) : Fin count → K :=
  CanonicalExtensionSampler.assemble basis (coefficients p (count * degree) values length)

theorem assemble_canonical_coordinate {p degree : ℕ} {K : Type}
    [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ)
    (values : List ℕ) (length : values.length = count * degree)
    (valid : ∀ v ∈ values, v < p) (element : Fin count) (coordinate : Fin degree) :
    (basis.equivFun (assemble basis count values length element) coordinate).val =
      values[coordinate.val + degree * element.val]'(by
        have := (finProdFinEquiv (element, coordinate)).isLt
        change coordinate.val + degree * element.val < count * degree at this
        omega) := by
  rw [assemble, CanonicalExtensionSampler.assemble_coordinate]
  exact coefficients_canonical p (count * degree) values length valid _

/-- The actual online request, including its final receipt, supplies the
length and canonical bounds needed for pure typed extension assembly. -/
theorem finished_request_coordinate {p degree : ℕ} {K : Type}
    [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (fuel count : ℕ)
    (transcript : NativeTranscript.Transcript) (label : InputIndexedOracle.Input)
    (world : InputIndexedOracle.World) (state : State) (result : NativeTranscript.Transcript)
    (finished : (OracleProgram.run (request p fuel transcript label (count * degree)) world).run.1 =
      .finished state result) (element : Fin count) (coordinate : Fin degree) :
    let length := request_finished_length p fuel transcript label (count * degree) world state result finished
    (basis.equivFun (assemble basis count state.values length element) coordinate).val =
      state.values[(finProdFinEquiv (element, coordinate)).val]'(by
        have _length := request_finished_length p fuel transcript label (count * degree) world state result finished
        omega) := by
  have valid := request_values_valid p fuel transcript label (count * degree) world
  rw [finished] at valid
  exact assemble_canonical_coordinate basis count state.values _ valid element coordinate

/-- Concrete native Goldilocks grouping, with three consecutive coefficients per value. -/
def goldilocks (count : ℕ) (values : List ℕ) (length : values.length = count * 3) :
    Fin count → NativeExtensionFields.Goldilocks3 :=
  assemble NativeExtensionFields.goldilocksBasis count values length

/-- Concrete native BabyBear grouping, with six consecutive coefficients per value. -/
def babyBear (count : ℕ) (values : List ℕ) (length : values.length = count * 6) :
    Fin count → NativeExtensionFields.BabyBear6 :=
  assemble NativeExtensionFields.babyBearBasis count values length

end

end FormalProof4FHE.HasteBoots.NativeFieldAssembly
