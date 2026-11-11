module
public import FormalProof4FHE.HasteBoots.CanonicalHelperFiber
@[expose] public section

/-! Equality of the original parameters, context/root keys and raw history
identifies complete packed public tables. Widths may be presented with
different dependent indices; all packing padding lanes are included. -/
namespace FormalProof4FHE.HasteBoots.PackedContextCongruence
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context)
noncomputable section

theorem packed (left right : Context) (parameters : left.parameters = right.parameters)
    (dummy leftContext rightContext leftRoot rightRoot : Digest) (context : leftContext = rightContext) (root : leftRoot = rightRoot)
    (leftHistory rightHistory : List Observation) (history : leftHistory = rightHistory) (radius : ℕ)
    (leftCapacity : GoldCommonSourceTable.Capacity left.parameters) (rightCapacity : GoldCommonSourceTable.Capacity right.parameters)
    (leftGeometry : GoldHistorySourceTable.Geometry left.parameters) (rightGeometry : GoldHistorySourceTable.Geometry right.parameters)
    {leftPadding rightPadding : ℕ} (leftWidth : left.parameters.width.val = 3+leftPadding) (rightWidth : right.parameters.width.val = 3+rightPadding) :
    HEq (ScalarPublicSourceModel.publicPacked left dummy leftContext leftRoot leftHistory radius leftCapacity leftGeometry leftWidth)
      (ScalarPublicSourceModel.publicPacked right dummy rightContext rightRoot rightHistory radius rightCapacity rightGeometry rightWidth) := by
  have padding : leftPadding = rightPadding := by
    have width := congrArg (fun parameters => parameters.width.val) parameters
    omega
  subst rightPadding
  subst rightContext
  subst rightRoot
  subst rightHistory
  cases left
  cases right
  cases parameters
  rfl

end
end FormalProof4FHE.HasteBoots.PackedContextCongruence
