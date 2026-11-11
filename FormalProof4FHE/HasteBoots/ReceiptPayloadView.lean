module
public import FormalProof4FHE.HasteBoots.NativeReceiptPrefixView
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
@[expose] public section

/-! Whole raw payloads named by receipt observations. Partial positive SHAKE
reads and hash queries expose their whole key; starts and empty reads do not.
This is a finite history view, not a receipt authentication claim. -/
namespace FormalProof4FHE.HasteBoots.ReceiptPayloadView
open InputIndexedOracle (Input Coordinate)
open NativeTranscript (Observation)
open NativeReceiptPrefixView (domain key)
open scoped Classical
noncomputable section

def read (input : Input) : Option Input :=
  if input.take domain.length = domain then some (input.drop domain.length) else none

theorem read_key (raw : Input) : read (key raw) = some raw := by
  simp only [read,key,List.take_left,List.drop_left,ite_true]

def candidate : Observation → Option Input
  | .start _ => none
  | .output input _ values => if values = [] then none else read input
  | .hash input _ => read input

def payloads (history : List Observation) : Finset Input := (history.filterMap candidate).toFinset

theorem observed (raw values : Input) (offset : ℕ) (history : List Observation)
    (positive : values ≠ []) (member : .output (key raw) offset values ∈ history) :
    raw ∈ payloads history := by
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨_,member,by simp only [candidate,positive,ite_false,read_key]⟩

theorem hashed (raw : Input) (digest : Input) (history : List Observation)
    (member : .hash (key raw) digest ∈ history) : raw ∈ payloads history := by
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨_,member,read_key raw⟩

theorem known (raw : Input) (position : ℕ) (history : List Observation)
    (coordinate : (.inl (key raw,position) : Coordinate) ∈ ObservationReplay.footprint history) :
    raw ∈ payloads history := by
  obtain ⟨entry,present,coordinate⟩ := Finset.mem_biUnion.mp coordinate
  cases entry with
  | start input => simp [ObservationReplay.coordinates] at coordinate
  | hash input digest => simp [ObservationReplay.coordinates] at coordinate
  | output input offset values =>
    have info := (NativeShakeProjection.output_coordinate input offset values _).mp coordinate
    have inputEq := info.1
    subst input
    apply observed raw values offset history _ (List.mem_toFinset.mp present)
    intro empty
    simp only [empty,List.length_nil] at info
    omega

theorem seen (raw : Input) (history : List Observation)
    (exposed : CausalStreamExposure.seen history (key raw) = true) : raw ∈ payloads history := by
  obtain ⟨entry,member,touches⟩ := List.any_eq_true.mp exposed
  cases entry with
  | start input => contradiction
  | hash input digest => contradiction
  | output input offset values =>
    obtain ⟨rfl,positive⟩ := of_decide_eq_true touches
    exact observed raw values offset history (by intro empty; simp [empty] at positive) member

theorem append (earlier later : List Observation) :
    payloads (earlier ++ later) = payloads earlier ∪ payloads later := by
  simp only [payloads,List.filterMap_append,List.toFinset_append]

theorem card (history : List Observation) : (payloads history).card ≤ history.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

end
end FormalProof4FHE.HasteBoots.ReceiptPayloadView
