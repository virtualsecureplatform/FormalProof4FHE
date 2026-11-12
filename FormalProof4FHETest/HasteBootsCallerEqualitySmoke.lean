module
import all FormalProof4FHE.HasteBoots.LookupInitialWork
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace HasteBootsCallerEqualitySmoke
open FormalProof4FHE.HasteBoots
open NativeExtensionFields (goldilocksBasis)
open HasteBootsSamplerAncestrySmoke (child roots worldZero worldReject)
noncomputable section

def initial (n : ℕ) := NativeLookupEquality.initial (K := NativeExtensionFields.Goldilocks3) n child roots (by decide +kernel)
def paused := NativeLookupEquality.execute goldilocksBasis 7 3 (initial 1) worldZero
def resumed := NativeLookupEquality.execute goldilocksBasis 7 1 paused.1 worldZero
def rejected := NativeLookupEquality.execute goldilocksBasis 7 5 (initial 1) worldReject
def completed := NativeLookupEquality.execute goldilocksBasis 7 8 (initial 1) worldZero
def emptyDimension := NativeLookupEquality.execute goldilocksBasis 7 2 (initial 0) worldZero

/-- An incomplete triple has raw reads but no exported equality draw. -/
theorem partial_triple : paused.1.active.map (fun field => (field.remaining,field.values.length)) = some (1,2) ∧
    paused.1.draws.length = 0 ∧ paused.2.length = 3 := by decide +kernel

/-- Completion after suspension retains all three original eight-byte reads. -/
theorem resumed_reads : resumed.1.draws.length = 1 ∧
    (paused.2++resumed.2).filterMap (fun entry => match entry with
      | .output _ _ values => if values.length = 8 then some values.length else none
      | _ => none) = [8,8,8] := by decide +kernel

/-- Rejected coefficients still expose the original stream in the actual log. -/
theorem rejected_exposure : rejected.1.draws.length = 0 ∧
    rejected.1.active.map (fun field => (field.values.length,
      CausalStreamExposure.seen rejected.2 field.phase.pending.input)) = some (0,true) := by decide +kernel

/-- Both stored original points have genuinely observed coefficient inputs. -/
theorem completed_exposure : completed.1.draws.length = 2 ∧
    (completed.1.draws.map (fun draw => CausalStreamExposure.seen completed.2 draw.coefficients.phase.pending.input)) =
      [true,true] := by decide +kernel

/-- A zero-dimensional point emits its receipt without exposing its field
input. Receipt reads alone cannot justify equality-stream first exposure. -/
theorem zero_dimension_receipt_only : emptyDimension.1.draws.length = 1 ∧
    (emptyDimension.1.draws.map (fun draw => CausalStreamExposure.seen emptyDimension.2 draw.coefficients.phase.pending.input)) =
      [false] := by decide +kernel

end
end HasteBootsCallerEqualitySmoke
