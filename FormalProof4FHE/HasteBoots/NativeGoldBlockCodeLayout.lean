module
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeMeaning
public import FormalProof4FHE.HasteBoots.ConcreteNTTGoldCacheRCU
@[expose] public section

/-! Literal arithmetic preflight of BlockReedSolomonCode::new, before every
backend call. It retains the original failure order and all stored dimensions.
The backend-driven constructor is separate; no Boolean table callback executes
inside this preflight. Actual usize/Rust/allocation refinement remains open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBlockCodeLayout
open NativeUsizeMessage (Usize)
open NativeGoldBlockCode (Error ceilBlocks nextLog paddedBlocks domainBlocks)

structure Layout where
  messageLength : Usize
  blockWidth : Usize
  messageBlocks : Usize
  blocks : Usize
  deriving DecidableEq

def logSize (layout : Layout) : ℕ := layout.blocks.val.size-1

def preflight (message block blowup : Usize) : Except Error Layout :=
  if valid : message.val ≠ 0 ∧ block.val ≠ 0 ∧ 2 ≤ blowup.val ∧ blowup.val = 2^(nextLog blowup.val) then
    let padded := paddedBlocks message.val block.val
    if fitsMessage : padded < 2^64 then
      if padded*blowup.val < 2^64 then
        let count := domainBlocks message.val block.val blowup.val
        if fitsCode : count*block.val < 2^64 then
          have fitsCount : count < 2^64 := by
            have positive : 0 < block.val := Nat.pos_of_ne_zero valid.2.1
            nlinarith
          .ok ⟨message,block,⟨padded,fitsMessage⟩,⟨count,fitsCount⟩⟩
        else .error .codewordOverflow
      else .error .domainOverflow
    else .error .messageOverflow
  else .error .dimensions

def store (layout : Layout) (root : NativeFieldRepresentation.GoldWord) : NativeGoldBlockCode.Stored :=
  ⟨layout.messageLength,layout.blockWidth,layout.messageBlocks,layout.blocks,NativeBrakedownContext.modulus,root⟩

theorem store_log (layout : Layout) (root : NativeFieldRepresentation.GoldWord) :
    NativeGoldBlockCode.logSize (store layout root) = logSize layout := rfl

theorem build_from_preflight (message block blowup : Usize) (layout : Layout)
    (ready : preflight message block blowup = .ok layout) (tables : NativeGoldBlockCode.Tables)
    (root : NativeGoldSolinas.Word) (generated : tables.generate (logSize layout) = true)
    (initialized : tables.initTable (logSize layout) = true) (loaded : tables.load (logSize layout) = some root) :
    NativeGoldBlockCode.build tables message block blowup = .ok (store layout (NativeGoldSolinas.raw root)) := by
  unfold preflight at ready
  unfold NativeGoldBlockCode.build
  split at ready
  · rename_i valid
    rw [dite_eq_left valid]
    dsimp only at ready ⊢
    split at ready
    · rename_i fitsMessage
      rw [dite_eq_left fitsMessage]
      split at ready
      · rename_i fitsDomain
        rw [ite_eq_left fitsDomain]
        split at ready
        · rename_i fitsCode
          rw [dite_eq_left fitsCode]
          cases ready
          simp only [logSize] at generated initialized loaded
          simp only [generated,initialized,loaded,ite_true]
          rfl
        · cases ready
      · cases ready
    · cases ready
  · cases ready

end FormalProof4FHE.HasteBoots.NativeGoldBlockCodeLayout
