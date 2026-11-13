module
public import FormalProof4FHE.HasteBoots.ConstructedGoldTargets
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
public import FormalProof4FHE.HasteBoots.HeterogeneousSingleOpening
public import FormalProof4FHE.HasteBoots.GoldContextInput
public import FormalProof4FHE.HasteBoots.NTTButterfly
@[expose] public section

/-! Canonical original-source decoder descriptors from completed native Gold
parameter construction. Test width and code-symbol width are checked public
metadata; rectangular helper roles are not silently identified with square
original-source workers. No decoded source values are constructor inputs. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldSourceDescriptor
open NativeGoldParameterStore (Entry GoodEntry)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored logSize)
open NativeFields (Goldilocks)
noncomputable section

abbrev Configuration := Parameters Stored

def heights (parameters : Configuration) : ℕ := logSize parameters.code

def layout (parameters : Configuration) : HeterogeneousSingleOpening.Layout :=
  ⟨parameters.leftVariables.val,parameters.numVariables.val-parameters.leftVariables.val,
    parameters.code.messageBlocks.val,parameters.queries.val⟩

theorem physical_dimensions (entry : Entry) (good : GoodEntry entry) :
    (layout entry.initialized.parameters).front + (layout entry.initialized.parameters).suffix =
      entry.initialized.parameters.numVariables.val := by
  have checked := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description entry.initialized.parameters
    entry.initialized.geometry (NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2)
  have ordered := checked.basic.2.1
  dsimp [layout]
  omega

theorem message_length (entry : Entry) (good : GoodEntry entry) :
    entry.initialized.parameters.code.messageLength.val = 2^(layout entry.initialized.parameters).suffix := by
  have checked := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description entry.initialized.parameters
    entry.initialized.geometry (NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2)
  exact checked.code.1

/-- Message coverage follows from the actual completed code constructor. -/
theorem symbol_capacity (entry : Entry) (good : GoodEntry entry) :
    entry.initialized.parameters.code.messageLength.val ≤
      entry.initialized.parameters.code.messageBlocks.val * entry.initialized.parameters.code.blockWidth.val :=
  (NativeGoldBlockCodeMeaning.constructor_dimensions (ConstructedGoldTargets.tables entry good)
    entry.request.message entry.request.block entry.request.blowup entry.initialized.parameters.code
    (ConstructedGoldTargets.entry_build entry good)).2.2.1

theorem degree_bounds (entry : Entry) (good : GoodEntry entry) :
    0 < (layout entry.initialized.parameters).m ∧
      (layout entry.initialized.parameters).m < 2^heights entry.initialized.parameters := by
  have checked := NativeGoldBlockCodeMeaning.constructor_dimensions (ConstructedGoldTargets.tables entry good)
    entry.request.message entry.request.block entry.request.blowup entry.initialized.parameters.code
    (ConstructedGoldTargets.entry_build entry good)
  exact ⟨checked.1,checked.2.1⟩

/-- A constructed power-of-two domain has the same Merkle and NTT height. -/
theorem height_of_power (exponent : ℕ) : NativeBrakedownParameters.height (2^exponent) = exponent := by
  apply Nat.le_antisymm
  · exact NativeBrakedownParameters.height_minimal _ _ le_rfl
  · exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (NativeBrakedownParameters.leaves_cover (2^exponent) (by positivity))

theorem geometry_height (entry : Entry) (good : GoodEntry entry) :
    entry.initialized.geometry.height = heights entry.initialized.parameters := by
  have checked := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description entry.initialized.parameters
    entry.initialized.geometry (NativeGoldParameterInitialization.parameter_geometry entry.header entry.config entry.initialized good.2)
  have power := (NativeGoldBlockCodeMeaning.constructor_log (ConstructedGoldTargets.tables entry good)
    entry.request.message entry.request.block entry.request.blowup entry.initialized.parameters.code
    (ConstructedGoldTargets.entry_build entry good)).2
  rw [checked.computed]
  change NativeBrakedownParameters.height entry.initialized.parameters.code.blocks.val = heights entry.initialized.parameters
  rw [power]
  exact height_of_power _

variable {b : ℕ}
/-- Square original-source workers use the actual native test and symbol
widths. Both equalities concern public retained fields. -/
theorem source_capacity (entry : Entry) (good : GoodEntry entry)
    (width : entry.initialized.parameters.width.val = b)
    (block : entry.initialized.parameters.code.blockWidth.val = b) :
    2^(layout entry.initialized.parameters).suffix ≤ (layout entry.initialized.parameters).m*b := by
  have same : entry.initialized.parameters.code.blockWidth.val = entry.initialized.parameters.width.val := block.trans width.symm
  calc
    2^(layout entry.initialized.parameters).suffix = entry.initialized.parameters.code.messageLength.val := (message_length entry good).symm
    _ ≤ entry.initialized.parameters.code.messageBlocks.val * entry.initialized.parameters.code.blockWidth.val := symbol_capacity entry good
    _ = entry.initialized.parameters.code.messageBlocks.val * entry.initialized.parameters.width.val := congrArg (_ * ·) same
    _ = (layout entry.initialized.parameters).m*b := congrArg (_ * ·) width

/-- Only retained public parameter data and its constructor-derived domain
and coverage proofs determine this descriptor. The radius stays fixed. -/
def make (parameters : Configuration)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue parameters.code.domainRoot) (2^(heights parameters+1)))
    (capacity : 2^(layout parameters).suffix ≤ (layout parameters).m*b) (radius : ℕ) :
    RecordedPaddedSource.Parameters Goldilocks Configuration heights b :=
  ⟨(layout parameters).front,(layout parameters).suffix,(layout parameters).m,parameters,
    NTTButterfly.domain (heights parameters) (NativeFieldRepresentation.goldValue parameters.code.domainRoot) primitive,capacity,radius⟩

def source (entry : Entry) (good : GoodEntry entry)
    (width : entry.initialized.parameters.width.val = b)
    (block : entry.initialized.parameters.code.blockWidth.val = b) (radius : ℕ) :
    RecordedPaddedSource.Parameters Goldilocks Configuration heights b :=
  make entry.initialized.parameters
    (NativeGoldParameterInitialization.code_primitive entry.header entry.request entry.config good.1 entry.initialized good.2)
    (source_capacity entry good width block) radius

/-- Equality of the complete public record determines the descriptor; the
constructor proofs cannot change the domain or decoder's fallback behavior. -/
theorem make_congr {left right : Configuration} (same : left = right)
    (leftPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue left.code.domainRoot) (2^(heights left+1)))
    (rightPrimitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue right.code.domainRoot) (2^(heights right+1)))
    (leftCapacity : 2^(layout left).suffix ≤ (layout left).m*b)
    (rightCapacity : 2^(layout right).suffix ≤ (layout right).m*b) (radius : ℕ) :
    make left leftPrimitive leftCapacity radius = make right rightPrimitive rightCapacity radius := by
  cases same
  rfl

theorem source_congr (left right : Entry) (leftGood : GoodEntry left) (rightGood : GoodEntry right)
    (same : left.initialized.parameters = right.initialized.parameters)
    (leftWidth : left.initialized.parameters.width.val = b) (rightWidth : right.initialized.parameters.width.val = b)
    (leftBlock : left.initialized.parameters.code.blockWidth.val = b) (rightBlock : right.initialized.parameters.code.blockWidth.val = b)
    (radius : ℕ) :
    source left leftGood leftWidth leftBlock radius = source right rightGood rightWidth rightBlock radius :=
  make_congr same _ _ _ _ radius

/-- The native context bytes encode all decoder metadata, including the
query quota and retained code object; equal heights alone are not used. -/
theorem source_congr_of_context (left right : Entry) (leftGood : GoodEntry left) (rightGood : GoodEntry right)
    (same : GoldContextInput.bytes left.initialized.parameters = GoldContextInput.bytes right.initialized.parameters)
    (leftWidth : left.initialized.parameters.width.val = b) (rightWidth : right.initialized.parameters.width.val = b)
    (leftBlock : left.initialized.parameters.code.blockWidth.val = b) (rightBlock : right.initialized.parameters.code.blockWidth.val = b)
    (radius : ℕ) :
    source left leftGood leftWidth leftBlock radius = source right rightGood rightWidth rightBlock radius :=
  source_congr left right leftGood rightGood (GoldContextInput.bytes_injective same) leftWidth rightWidth leftBlock rightBlock radius

/-- Logical high-zero padding is derived from the actual physical dimensions. -/
theorem logical_padding (entry : Entry) (good : GoodEntry entry) (logical : ℕ)
    (fits : logical ≤ entry.initialized.parameters.numVariables.val) :
    (entry.initialized.parameters.numVariables.val-logical)+logical =
      (layout entry.initialized.parameters).front + (layout entry.initialized.parameters).suffix := by
  rw [physical_dimensions entry good]
  omega

end
end FormalProof4FHE.HasteBoots.ConstructedGoldSourceDescriptor
