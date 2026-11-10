module
public import FormalProof4FHE.HasteBoots.LookupPreflightPCSGeometry
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
@[expose] public section

/-! Native block-code construction at the original packing width derives the
PCS coefficient capacity and degree bounds. Parameter construction supplies its
own message length; no padding/count or width-equality certificate is assumed.
Domain/root generation and encoder/distance semantics remain separate. -/
namespace FormalProof4FHE.HasteBoots.LookupPCSCodeCapacity
open NativeGoldBlockCode (Stored Tables logSize description)
open NativeBrakedownContext (Parameters)
open NativeUsizeMessage (Usize)

/-- Native tree height for a genuinely constructed power-of-two block domain. -/
theorem height_power (exponent : ℕ) : NativeBrakedownParameters.height (2 ^ exponent) = exponent := by
  apply Nat.le_antisymm
  · exact NativeBrakedownParameters.height_minimal _ _ le_rfl
  · have covers := NativeBrakedownParameters.leaves_cover (2 ^ exponent) (by positivity)
    by_contra rejected
    have smaller : NativeBrakedownParameters.height (2 ^ exponent) < exponent := by omega
    have strict := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr smaller
    exact (Nat.not_le_of_gt strict) covers

structure Spec (parameters : Parameters Stored) (geometry : NativeBrakedownParameters.Geometry) : Prop where
  blockWidth : parameters.code.blockWidth = parameters.width
  capacity : 2 ^ (parameters.numVariables.val - parameters.leftVariables.val) ≤
    parameters.code.messageBlocks.val * parameters.width.val
  degreePositive : 0 < parameters.code.messageBlocks.val
  degreeLessBlocks : parameters.code.messageBlocks.val < parameters.code.blocks.val
  height : geometry.height = logSize parameters.code
  degreeLeaves : parameters.code.messageBlocks.val ≤ 2 ^ geometry.height

/-- The actual code constructor is invoked at the original object's packed
width. Its output and the actual parameter constructor derive every bound. -/
theorem code_spec (tables : Tables) (message blowup : Usize) (parameters : Parameters Stored)
    (constructed : NativeGoldBlockCode.build tables message parameters.width blowup = .ok parameters.code)
    (geometry : NativeBrakedownParameters.Geometry)
    (built : NativeBrakedownParameters.build description parameters = some geometry) : Spec parameters geometry := by
  have code := NativeGoldBlockCode.build_spec tables message parameters.width blowup parameters.code constructed
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions tables message parameters.width blowup parameters.code constructed
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log tables message parameters.width blowup parameters.code constructed).2
  have native := NativeBrakedownParameters.build_spec description parameters geometry built
  have heightEq : geometry.height = logSize parameters.code := by
    rw [native.computed]
    change NativeBrakedownParameters.height parameters.code.blocks.val = logSize parameters.code
    rw [blocks,height_power]
  refine ⟨code.blockEq,?_,dimensions.1,?_,heightEq,?_⟩
  · have capacity := dimensions.2.2.1
    have messageLength : parameters.code.messageLength.val =
        2 ^ (parameters.numVariables.val - parameters.leftVariables.val) := native.code.1
    rw [code.blockEq,messageLength] at capacity
    exact capacity
  · rw [blocks]
    exact dimensions.2.1
  · rw [heightEq]
    exact Nat.le_of_lt dimensions.2.1

end FormalProof4FHE.HasteBoots.LookupPCSCodeCapacity
