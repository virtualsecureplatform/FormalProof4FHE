module

public import FormalProof4FHE.HasteBoots.NTTButterfly
public import FormalProof4FHE.HasteBoots.BlockEncoder

@[expose] public section

/-!
# Per-coordinate padded NTT encoding equals the PCS polynomial encoder

Native block-RS encoding initializes an N-element zero buffer, copies the m
message coefficients for one lane, transforms it, and interleaves the outputs.
The exact-arithmetic butterflies give the same word as BlockEncoder on the
injective bit-reversed odd-root domain. Machine buffers, lazy field residues
and the optimized Rust/concrete-ntt kernel still need refinement.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NTTBlockEncoder

variable {F : Type} [Field F] {m b n : ℕ}

def padded (coefficients : Fin m → F) (index : Fin (2 ^ n)) : F :=
  if inside : index.val < m then coefficients ⟨index.val, inside⟩ else 0

/-- Zero initialization and prefix copy preserve the message polynomial. -/
theorem evaluate_padded (enough : m ≤ 2 ^ n) (coefficients : Fin m → F) (point : F) :
    NTTButterfly.evaluate (n := n) (padded (n := n) coefficients) point = ∑ index, coefficients index * point ^ index.val := by
  let term : ℕ → F := fun index => if inside : index < m then coefficients ⟨index, inside⟩ * point ^ index else 0
  have extent : (∑ index ∈ Finset.range (2 ^ n), term index) = ∑ index ∈ Finset.range m, term index := by
    symm
    apply Finset.sum_subset (Finset.range_mono enough)
    intro index _ outside
    simp only [Finset.mem_range] at outside
    simp [term, outside]
  have first : NTTButterfly.evaluate (n := n) (padded (n := n) coefficients) point = ∑ index ∈ Finset.range (2 ^ n), term index := by
    unfold NTTButterfly.evaluate
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro index _
    by_cases inside : index.val < m <;> simp [padded, term, inside]
  rw [first, extent, ← Fin.sum_univ_eq_sum_range]
  simp only [term, Fin.isLt, dite_eq_left]

/-- One base-field buffer per lane; output symbols are lane-minor. -/
def encode (psi : F) (input : Fin m → Fin b → F) : Fin (2 ^ n) → Fin b → F :=
  fun position lane => NTTButterfly.flatTransform n psi (psi ^ 2) (padded (fun index => input index lane)) position

/-- No encoder-refinement certificate is assumed for the field butterfly
algorithm: the exact source layout and all zero padding are proved here. -/
theorem encode_eq (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (enough : m ≤ 2 ^ n) (input : Fin m → Fin b → F) :
    encode psi input = BlockEncoder.encode (NTTButterfly.domain n psi root) input := by
  funext position lane
  rw [encode, NTTButterfly.negacyclic_evaluation n psi root]
  change NTTButterfly.evaluate (padded (fun index => input index lane)) (NTTButterfly.nodes n psi position) = _
  exact evaluate_padded enough _ _

/-- Exact arithmetic native-layout codewords land in the actual distance code. -/
theorem encode_mem_code [NeZero b] (psi : F) (root : IsPrimitiveRoot psi (2 ^ (n + 1)))
    (enough : m ≤ 2 ^ n) (input : Fin m → Fin b → F) :
    encode psi input ∈ BlockCode.code (NTTButterfly.domain n psi root) m b := by
  rw [encode_eq psi root enough]
  exact BlockEncoder.encode_mem_code _ _

end FormalProof4FHE.HasteBoots.NTTBlockEncoder
