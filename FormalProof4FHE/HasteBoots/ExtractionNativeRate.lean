module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound
@[expose] public section

/-! The executed native extraction arithmetic formula, uniformly bounded over
adaptive private-memory branches without a conditional security certificate. -/
namespace FormalProof4FHE.HasteBoots.ExtractionNativeRate
noncomputable section
open NativeRootMessage (Digest)
variable {q c lanes : ℕ} [Fact q.Prime]
  {K Cfg Input Response Memory CommitMemory : Type}
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}
variable (base : Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := c) (lanes := lanes)
  (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := H))
  (radius : Memory → Unit → ℕ)

/-- Native first/round arithmetic errors plus the original coefficient opening. -/
def rate (memory : Memory) : ENNReal :=
  (((c : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
    ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
    (c : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
  (([()]).map (fun factor => JointMatrixOpening.error (K := K) (m := ((base memory).code factor).m) (b := 2^lanes)
    (queries := ((base memory).code factor).queries) ((base memory).domain factor) (radius memory factor))).sum

/-- Uniform rate over the actual factory's memory-dependent code descriptors. -/
def bound : ENNReal := ⨆ memory, rate (K := K) base radius memory

omit [DecidableEq Input] [DecidableEq Digest] [Fintype K] in
/-- The native formula at every selected memory is bounded by the supremum. -/
theorem le_bound (memory : Memory) : rate (K := K) base radius memory ≤ bound (K := K) base radius :=
  le_iSup (fun memory => rate (K := K) base radius memory) memory

end
end FormalProof4FHE.HasteBoots.ExtractionNativeRate
