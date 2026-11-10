module
import all FormalProof4FHE.HasteBoots.SingleOpeningFieldInputView
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleChallengeSmoke
open SingleOpeningFieldInputView
open NativeFieldRepresentation (GoldWord)
open NativeLookupRequestWire (Row)

def zero : Row := ⟨[0],by decide⟩
def lazyZero : Row := ⟨[⟨NativeFields.goldilocksModulus,by decide +kernel⟩],by decide⟩
def data : Data := ⟨(fun _ => 0),(fun _ => 7),⟨[],by decide⟩,lazyZero⟩
def view : View := ⟨[],data,⟨1,by decide⟩⟩

/-- Structural recovery retains the original raw lazy word and original root. -/
example : (parse (TranscriptFrame.encodeMany view.frames)).map
    (fun parsed => (parsed.data.root 0,parsed.data.claimed.val.map Fin.val,parsed.count.val)) =
    some (7,[NativeFields.goldilocksModulus],1) := by decide +kernel

/-- Count zero is rejected; it cannot instantiate a first-field experiment. -/
example : (parse (TranscriptFrame.encodeMany ({view with count := ⟨0,by decide⟩}).frames)).isNone = true := by decide +kernel

/-- The batch label cannot stand in for the original single-opening request. -/
example : (parse (TranscriptFrame.encodeMany [contextFrame data,openingFrame data,typedFrame,primeFrame,
    {fieldFrame view.count with label := NativeGoldBatchPrelude.randomLabel}])).isNone = true := by decide +kernel

/-- A matching context earlier in the transcript does not repair nonadjacency. -/
example : (parse (TranscriptFrame.encodeMany [contextFrame data,⟨1,[],[]⟩,openingFrame data,typedFrame,primeFrame,
    fieldFrame view.count])).isNone = true := by decide +kernel

example : (readBinding (contextFrame data) {openingFrame data with message := (openingFrame data).message++[0]}).isNone = true := by decide +kernel
example : (parse (TranscriptFrame.encodeMany view.frames++[255])).isNone = true := by decide +kernel

/-- Equal field spellings still bind different original raw response packets. -/
example : SingleOpeningColumnLaw.boundInput ⟨[],fun _ => 0⟩ [1] ⟨2,by decide⟩ ⟨1,by decide⟩
    ⟨zero,zero,⟨[],by decide⟩⟩ ≠
    SingleOpeningColumnLaw.boundInput ⟨[],fun _ => 0⟩ [1] ⟨2,by decide⟩ ⟨1,by decide⟩
      ⟨lazyZero,zero,⟨[],by decide⟩⟩ := by
  intro same
  have rows := (SingleOpeningColumnLaw.boundInput_eq_iff _ _ _ _ _ _).mp same
  have impossible := congrArg (fun row : Row => row.val.map Fin.val) rows.1
  exact (by decide +kernel : [0] ≠ [NativeFields.goldilocksModulus]) impossible

end FormalProof4FHE.HasteBoots.SingleChallengeSmoke
