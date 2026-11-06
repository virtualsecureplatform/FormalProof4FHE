module
public import FormalProof4FHE.HasteBoots.NativeIndexFirstReadLaw
@[expose] public section

/-! Typed ordered index values depend on the complete request input and
checked dimensions, not a supplied draw or receipt-knowledge certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeIndexInputValues
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript)
open NativeUsizeMessage (Usize)
open OracleProgram (run)

theorem input_congr (bits : ℕ) (first second : Transcript) (label : Input) (domain count : Usize)
    (valid : NativeIndexRequest.check domain count = true)
    (same : NativePrequeryIndexLaw.requestInput first label domain count = NativePrequeryIndexLaw.requestInput second label domain count)
    (world : World) :
    NativeIndexFirstReadLaw.values bits first label domain count world = NativeIndexFirstReadLaw.values bits second label domain count world := by
  unfold NativeIndexFirstReadLaw.values
  rw [NativePrequeryIndexLaw.request_run world first label domain count valid,
    NativePrequeryIndexLaw.request_run world second label domain count valid]
  simp only [NativePrequeryIndexLaw.outcome,Option.bind_some]
  rw [same]
end FormalProof4FHE.HasteBoots.NativeIndexInputValues
