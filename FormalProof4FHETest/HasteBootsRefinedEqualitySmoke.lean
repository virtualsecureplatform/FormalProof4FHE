module
import all FormalProof4FHE.HasteBoots.NativeParentInputView
import all FormalProof4FHE.HasteBoots.NativeForkAncestry
import all Init.Data.String.Defs
import all FormalProof4FHE.HasteBoots.SafeEqualityClassKernel
import all FormalProof4FHETest.HasteBootsEqualityFamilySmoke

namespace HasteBootsRefinedEqualitySmoke
open FormalProof4FHE.HasteBoots
open NativeExtensionFields (goldilocksBasis)
open HasteBootsSamplerAncestrySmoke (parent child roots worldReject)
open HasteBootsGoldEqualityPointSmoke (equality)
open HasteBootsEqualityFamilySmoke (repeated)
noncomputable section

private theorem not_seed (frames : List TranscriptFrame.Frame)
    (kind : frames.reverse.head?.map TranscriptFrame.Frame.kind = some 4) : ¬NativeParentInputView.isSeedFrames frames := by
  cases reverse : frames.reverse with
  | nil => simp [NativeParentInputView.isSeedFrames,reverse]
  | cons first rest =>
    cases rest with
    | nil => simp [NativeParentInputView.isSeedFrames,reverse]
    | cons second tail =>
      have firstKind : first.kind = 4 := by simpa only [reverse,List.head?_cons,Option.map_some,Option.some.injEq] using kind
      simp [NativeParentInputView.isSeedFrames,reverse,firstKind]

private theorem reject (input : InputIndexedOracle.Input)
    (complete : (TranscriptFrame.decodeAll input).isSome = true)
    (kind : ((TranscriptFrame.decodeAll input).get complete).reverse.head?.map TranscriptFrame.Frame.kind = some 4) :
    NativeParentInputView.parseParent input = none := by
  rw [NativeParentInputView.parseParent,← Option.some_get complete,Option.bind_some,ite_eq_right (not_seed _ kind)]

theorem first_input_not_parent : NativeParentInputView.parseParent
    (equality.draws[0]'(by decide +kernel)).coefficients.phase.pending.input = none := by
  apply reject _ (by decide +kernel)
  decide +kernel

theorem later_input_not_parent : NativeParentInputView.parseParent
    (equality.draws[1]'(by decide +kernel)).coefficients.phase.pending.input = none := by
  apply reject _ (by decide +kernel)
  decide +kernel

theorem zero_dimension_input_not_parent : NativeParentInputView.parseParent
    (repeated.draws[0]'(by decide +kernel)).coefficients.phase.pending.input = none := by
  apply reject _ (by decide +kernel)
  decide +kernel

def suspended := (NativeLookupEquality.execute goldilocksBasis 7 2
  (NativeLookupEquality.initial 1 child roots (by decide +kernel)) worldReject).1

theorem rejected_reader_keeps_suffix : suspended.active.isSome = true ∧
    NativeParentInputView.parseParent (suspended.active.get (by decide +kernel)).phase.pending.input = none ∧
    (suspended.active.get (by decide +kernel)).phase.consumed.length = 8 := by
  refine ⟨by decide +kernel,?_,by decide +kernel⟩
  apply reject _ (by decide +kernel)
  decide +kernel

/-- Separation is specific to equality keys: a native fork request is still
recognized by the same parent parser. -/
theorem native_parent_recognized :
    (NativeParentInputView.parseParent (NativeForkAncestry.seedInput parent [] [])).isSome = true := by
  let frames := (TranscriptFrame.decodeAll parent.input).getD []
  have bytes : parent.input = TranscriptFrame.encodeMany frames := by decide +kernel
  have decoded : TranscriptFrame.decodeAll parent.input = some frames := by decide +kernel
  have valid := (TranscriptFrame.decodeAll_sound parent.input frames decoded).1
  rw [NativeForkAncestry.seedInput_parsed parent frames [] [] bytes valid (by decide +kernel) (by decide +kernel)]
  rfl

end
end HasteBootsRefinedEqualitySmoke
