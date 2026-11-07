module
public import FormalProof4FHE.HasteBoots.ExecutableSourceHistory
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFirstFieldSource
@[expose] public section
namespace FormalProof4FHE.HasteBoots.ExecutableSourceSelection
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeCanonicalLookupWire (Source)
open NativeTranscript (Observation)
open ExecutableSourceHistory (State Log project reconstruct)
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-! Executable selection of the original common snapshot at the native source
boundary. Full mixed prefixes, partially observed seeds, old aliases and every
height are retained. This does not establish application registry ownership. -/
def contains (state : State) (key : Source) (log : Log) : Bool :=
  (List.finRange 64).all (fun index => state.snapshots.any (fun entry =>
    decide (entry.1 = (key.1,index) ∧ entry.2.root = key.2 ∧ entry.2.cumulativeLog = log)))

def select (state : State) (key : Source) : Log :=
  if key ∈ state.ledger.frozen then
    ((state.snapshots.map (fun entry => entry.2.cumulativeLog)).find? (contains state key)).getD state.hashes
  else state.hashes

theorem contains_eq (state : NativeRootFamilyState.State) (key : Source) (log : Log) :
    contains (project state) key log = NativeRootFamilySourceSelection.contains state key log := rfl

theorem select_eq (state : NativeRootFamilyState.State) (key : Source) :
    select (project state) key = NativeRootFamilySourceSelection.select state key := rfl

def selected (before : List Observation) (field : NativeGoldBatchFieldInputView.View) : Log :=
  select (reconstruct before) (field.data.context,field.data.root)

theorem selected_eq (dummy : Digest) (before : List Observation) (field : NativeGoldBatchFieldInputView.View) :
    selected before field = NativeGoldBatchSelectedSource.log dummy before field := by
  unfold selected
  rw [ExecutableSourceHistory.reconstruct_eq NativeGoldColumnAuthentication.encoding dummy]
  exact select_eq _ _

def recover (history : List Observation) (field : NativeGoldBatchFieldInputView.View) : Option Log :=
  (CausalFirstStreamPrefix.recover (TranscriptFrame.encodeMany field.frames) history).map (fun before => selected before field)

theorem recover_eq (dummy : Digest) (history : List Observation) (field : NativeGoldBatchFieldInputView.View) :
    recover history field = NativeGoldBatchFirstFieldSource.recover dummy history field := by
  simp only [recover,NativeGoldBatchFirstFieldSource.recover,NativeGoldBatchFirstFieldSource.input]
  congr 1
  funext before
  exact selected_eq dummy before field
end FormalProof4FHE.HasteBoots.ExecutableSourceSelection
