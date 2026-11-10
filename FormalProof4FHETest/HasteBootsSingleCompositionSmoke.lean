module
import all FormalProof4FHE.HasteBoots.SingleOpeningWitnessedColumnBound
import all FormalProof4FHE.HasteBoots.SingleOpeningRecoveredMatrix
import all FormalProof4FHETest.HasteBootsSingleLinkSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleCompositionSmoke
open InputIndexedOracle (Input World)
open SingleLinkSmoke (field opening quote nonce)

def decoded := SingleOpeningPreparedChallenge.view field opening NativeGoldPcsColumns.label
  ⟨8,by decide⟩ ⟨2,by decide⟩ quote

theorem parsed : SingleOpeningChallengeLink.parse (nonce quote) = some decoded :=
  SingleOpeningPreparedChallenge.parse_native field (fun _ => 0) opening NativeGoldPcsColumns.label
    ⟨8,by decide⟩ ⟨2,by decide⟩ quote (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold TranscriptFrame.Valid; decide +kernel)

/-- Separation uses exact single-opening bytes even for an uncertified quote. -/
example : (decoded.field.phase (fun _ => 0)).pending.input.length < (nonce quote).length :=
  SingleOpeningChallengeScope.field_shorter _ _ parsed _

example : (decoded.field.phase (fun _ => 0)).pending.input ≠ nonce quote :=
  SingleOpeningChallengeScope.field_ne_column _ _ parsed _

def zeros : World := fun _ => 0
def rejected : World := fun _ => 255

def collect (fuel : ℕ) (world : World) := SingleOpeningFieldColumnLaw.collected (fun _ => 0) fuel decoded world

/-- Suspension is retained rather than discarded by normalization. -/
example : ((collect 0 zeros).1.remaining,(collect 0 zeros).1.values,(collect 0 zeros).2.length) = (1,[],0) := by decide +kernel

example : ((collect 1 zeros).1.remaining,(collect 1 zeros).1.values,(collect 1 zeros).1.phase.consumed.length) = (0,[0],8) := by decide +kernel

/-- A rejected candidate consumes bytes and remains incomplete. -/
example : ((collect 1 rejected).1.remaining,(collect 1 rejected).1.values,(collect 1 rejected).1.phase.consumed.length) = (1,[],8) := by decide +kernel

/-- Further rejected candidates remain part of the same reader/history. -/
example : ((collect 2 rejected).1.remaining,(collect 2 rejected).1.values,(collect 2 rejected).1.phase.consumed.length) = (1,[],16) := by decide +kernel

/-- Arbitrary collector budgets/worlds preserve an untouched column stream;
starts and empty column reads do not constitute earlier positive exposure. -/
example (fuel : ℕ) (world : World) : CausalStreamExposure.seen
    ([.start (nonce quote),.output (nonce quote) 93 []] ++ (collect fuel world).2) (nonce quote) = false := by
  exact SingleOpeningChallengeScope.unseen_after_collect _ _ parsed _ fuel world _
    (by simp [CausalStreamExposure.seen,CausalStreamExposure.touches])

end FormalProof4FHE.HasteBoots.SingleCompositionSmoke
