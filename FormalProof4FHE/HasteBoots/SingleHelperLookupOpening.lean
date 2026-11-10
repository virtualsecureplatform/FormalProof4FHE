module
public import FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
public import FormalProof4FHE.HasteBoots.SharedLookupTerminal
@[expose] public section

/-! A checked common-point terminal needs one helper coefficient opening.
The sum and identity obligations coincide after the actual sum/helper check.
These are opening-data equivalences, not a replacement batch transcript. -/
namespace FormalProof4FHE.HasteBoots.SingleHelperLookupOpening
open PackedSumcheckSubclaim
open MixedWidthLookupOpeningFamily (Packet pairPacket)
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count jobs : ℕ}

/-- Exactly one raw source claim per selected slot and one coefficient-helper
claim. Physical source and helper widths remain independent. -/
def Wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (point : Fin (c + row) → K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claims : Fin count → Fin (d + padding) → F) (helper : K) : Prop :=
  (∃ column, claims column ≠ (ExtensionLookupTerminal.sourceQuery basis shape point).query.fold (sources column)) ∨
    PaddedExtension.encode (padding := helperPadding) basis helper ≠
      (ExtensionQuery.coefficientsQuery basis point).query.fold helpers

/-- Common-point construction fixes both helper queries to the same query,
independently of whether the sum/helper value check passes. -/
theorem helper_query_eq (basis : Module.Basis (Fin d) F K)
    (g : MixedWidthLookupOpeningFamily.Geometry c row count jobs)
    (packet : Packet F K (d + padding) count (c + row) jobs) (job : Fin jobs) (claim : Fin 2) :
    MixedWidthLookupOpeningFamily.helperQuery (helperPadding := helperPadding) basis g packet job claim =
      PackedQueryArity.query (g.helperArity job).symm (ExtensionQuery.coefficientsQuery basis packet.point).query := by
  simp only [MixedWidthLookupOpeningFamily.helperQuery,ite_self]

theorem helper_value_eq (basis : Module.Basis (Fin d) F K)
    (g : MixedWidthLookupOpeningFamily.Geometry c row count jobs)
    (packet : Packet F K (d + padding) count (c + row) jobs) (job : Fin jobs)
    (matched : packet.sumExpected job = packet.helpers job) (claim : Fin 2) :
    MixedWidthLookupOpeningFamily.values (helperPadding := helperPadding) basis g packet (.inr job) claim =
      PaddedExtension.encode (padding := helperPadding) basis (packet.helpers job) := by
  funext lane
  by_cases first : claim = 0
  · simp [MixedWidthLookupOpeningFamily.values, first, matched]
  · simp [MixedWidthLookupOpeningFamily.values, first]

/-- No helper packet is duplicated: after the checked equality, either
logical helper failure is precisely the single original helper failure. -/
theorem wrong_iff {columns : Fin jobs → ℕ}
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (packet : Packet F K (d + padding) count (c + row) jobs)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (job : Fin jobs) (matched : packet.sumExpected job = packet.helpers job) :
    MixedWidthLookupOpeningFamily.WrongOpenings basis shape
      (fun column => sources (slots job column)) (helpers job)
      (pairPacket slots packet job).sumClaim (pairPacket slots packet job).zeroClaim
      (pairPacket slots packet job).values.sources (pairPacket slots packet job).values.helper ↔
    Wrong basis shape packet.point (fun column => sources (slots job column)) (helpers job)
      (fun column => packet.sources (slots job column)) (packet.helpers job) := by
  simp only [MixedWidthLookupOpeningFamily.WrongOpenings,Wrong,pairPacket,ScalarSumcheckQuery.point_query,matched]
  tauto

/-- Equality needed for the collapse is derived from the actual computed guard,
not supplied by the prover as a source/PCS certificate. -/
theorem guard_wrong_iff {columns : Fin jobs → ℕ}
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (packet : Packet F K (d + padding) count (c + row) jobs)
    (accepted : SharedLookupTerminal.guard basis shape slots pairs active enough packet = true)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : Fin jobs → MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F) :
    (∃ job, MixedWidthLookupOpeningFamily.WrongOpenings basis shape
      (fun column => sources (slots job column)) (helpers job)
      (pairPacket slots packet job).sumClaim (pairPacket slots packet job).zeroClaim
      (pairPacket slots packet job).values.sources (pairPacket slots packet job).values.helper) ↔
    ∃ job, Wrong basis shape packet.point (fun column => sources (slots job column)) (helpers job)
      (fun column => packet.sources (slots job column)) (packet.helpers job) := by
  apply exists_congr
  intro job
  exact wrong_iff basis shape slots packet sources helpers job
    (SharedLookupTerminal.guard_spec basis shape slots pairs active enough packet accepted job).1

end
end FormalProof4FHE.HasteBoots.SingleHelperLookupOpening
