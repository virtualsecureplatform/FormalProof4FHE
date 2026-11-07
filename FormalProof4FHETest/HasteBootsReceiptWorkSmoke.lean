module
import all FormalProof4FHE.HasteBoots.ClosedByteMachineReceiptWork
import all FormalProof4FHETest.HasteBootsCalibrationSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte World)
open ClosedByteMachine (Instruction Tape)
namespace HasteBootsReceiptWorkSmoke
noncomputable section

def raw : Fin 72 → Byte := fun _ => 0
def receiptKey : Input := NativeReceiptPrefixView.key (List.ofFn raw ++ [])
theorem parsed : NativeReceiptPrefixView.read 72 receiptKey = some raw :=
  NativeReceiptPrefixView.read_native 72 raw []

-- One partial read names a full raw-prefix guess; duplicate keys remain one guess.
example : (NativeReceiptPrefixView.guesses 72
    [.output receiptKey 63 [0],.output receiptKey 0 [1]]).card = 1 := by
  simp only [NativeReceiptPrefixView.guesses,NativeReceiptPrefixView.candidate,
    List.cons_ne_nil,ite_false,parsed,List.filterMap_cons,List.filterMap_nil,
    List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.pair_eq_singleton,Finset.card_singleton]

-- Hash keys also name candidates. Starts and empty reads do not.
example (world : World) : (NativeReceiptPrefixView.guesses 72
    [.hash receiptKey (List.ofFn (InputIndexedOracle.sha512 world receiptKey))]).card = 1 := by
  simp only [NativeReceiptPrefixView.guesses,NativeReceiptPrefixView.candidate,parsed,
    List.filterMap_cons,List.filterMap_nil,List.toFinset_cons,List.toFinset_nil,
    Finset.insert_empty,Finset.card_singleton]
example : NativeReceiptPrefixView.guesses 72 [.start receiptKey,.output receiptKey 71 []] = ∅ := by
  simp only [NativeReceiptPrefixView.guesses,NativeReceiptPrefixView.candidate,ite_true,
    List.filterMap_cons,List.filterMap_nil,List.toFinset_nil]

example : 1/((2^256 : ℕ) : ENNReal)+ClosedByteMachineReceiptWork.rate (2^256) ≤ 1/(2 : ENNReal)^255 :=
  ClosedByteMachineReceiptWork.rate_256
example (code : List Instruction) (publicData : Input) (old : ClosedByteMachineGoldRisk.Packet) :
    ClosedByteMachineReceiptWork.lowRisk code publicData 0 old = 0 := by
  simp only [ClosedByteMachineReceiptWork.lowRisk,Nat.not_lt_zero,ite_false]

example (code : List Instruction) (publicData : Input) (profile : NativeRootMessage.Digest) (privateData : Tape → Input) :
    InputIndexedOracle.law {world | ∃ fuel, NativeEarlyReceiptBound.event profile
      (ClosedByteMachineRequest.command code publicData) (ClosedByteMachineGoldRisk.history code publicData privateData fuel world).run world} ≤
      (1/(2 : ENNReal)^255)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  ClosedByteMachineReceiptWork.lifetime_le_255 code publicData profile privateData

open HasteBootsCalibrationSmoke (ctx tables constructed primitive compatible)
open HasteBootsBatchMeaningSmoke (usize)
example (code : List Instruction) (publicData : Input) (privateData : Tape → Input) :
    InputIndexedOracle.law {world | ∃ fuel,
      ClosedByteMachineGoldRisk.event code publicData (fun _ => 0) ctx primitive .helper (fun _ => 0)
        (ClosedByteMachineGoldRisk.history code publicData privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event (fun _ => 0) (ClosedByteMachineRequest.command code publicData)
        (ClosedByteMachineGoldRisk.history code publicData privateData fuel world).run world} ≤
      ((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  ClosedByteMachineReceiptWork.gold_exposure_lifetime_le_work code publicData (fun _ => 0) ctx tables
    (usize 2048) (usize 4) (usize 2) constructed primitive .helper compatible (fun _ => 0) privateData
end
end HasteBootsReceiptWorkSmoke
