module
import FormalProof4FHE.HasteBoots.NativeRecordValues

namespace FormalProof4FHETest.HasteBootsRecordValuesSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordValues

private def aggregate : Value := .record 7 (.pair (.scalar (.usize ⟨11,by decide⟩)) (.scalar (.usize ⟨22,by decide⟩)))
private def shape : Ty := .record 7 (.pair (.scalar .usize) (.scalar .usize))

example : get aggregate [.unwrap 7,.left] = some (.scalar (.usize ⟨11,by decide⟩)) := by decide
example : get aggregate [.unwrap 8,.left] = none := by decide
example : typeAt shape [.unwrap 7,.right] = some (.scalar .usize) := by decide
example : typeAt shape [.unwrap 8,.right] = none := by decide

example : (do
    let (selected,changed) ← take aggregate [.unwrap 7,.left]
    pure (selected, get changed [.unwrap 7,.left], get changed [.unwrap 7,.right], get changed [],
      compatible shape changed, fits shape changed)) =
    some (.scalar (.usize ⟨11,by decide⟩),none,some (.scalar (.usize ⟨22,by decide⟩)),none,true,false) := by decide

example : copyable (.record 9 (.pair (.scalar (.reference true)) (.scalar .usize))) = false := by decide
example : copyable (.record 9 (.pair (.scalar (.reference false)) (.scalar .usize))) = true := by decide
example : fits (.enumeration 4 [⟨1,by decide⟩,⟨2,by decide⟩,⟨8,by decide⟩]) (.enumeration 4 ⟨3,by decide⟩) = false := by decide
example : fits (.enumeration 4 [⟨8,by decide⟩]) (.enumeration 5 ⟨8,by decide⟩) = false := by decide
example : fits .nonnull (.scalar (.raw ⟨⟨⟨0,by decide⟩,none⟩,none⟩)) = false := by decide
example : fits .nonnull (.scalar (.raw ⟨⟨⟨64,by decide⟩,none⟩,none⟩)) = true := by decide
example : fits shape (.record 7 (.pair (.scalar (.usize ⟨11,by decide⟩)) .uninit)) = false := by decide

end FormalProof4FHETest.HasteBootsRecordValuesSmoke
