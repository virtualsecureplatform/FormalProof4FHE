module
public import FormalProof4FHE.HasteBoots.NativeByteCodec
public import FormalProof4FHE.HasteBoots.NativeShakeProjection
@[expose] public section

/-! Raw field-byte prefixes named by receipt query keys. Any positive partial
read of a receipt reveals its complete key; no full64-byte receipt read is
required. Starts and empty reads add no candidates. This view is not a work
metric or an authentication assertion. -/
namespace FormalProof4FHE.HasteBoots.NativeReceiptPrefixView
open InputIndexedOracle (Input Byte Coordinate)
open NativeTranscript (Observation)
open scoped Classical
noncomputable section

def domain : Input := NativeTranscript.utf8 "HasteBoots consumed field bytes v1"
def key (consumed : Input) : Input := domain ++ consumed

def read (count : ℕ) (input : Input) : Option (Fin count → Byte) :=
  if input.take domain.length = domain then ((NativeByteCodec.fixed count).read (input.drop domain.length)).map Prod.fst else none

theorem read_native (count : ℕ) (raw : Fin count → Byte) (tail : Input) :
    read count (key (List.ofFn raw ++ tail)) = some raw := by
  simp only [read,key,List.take_left,List.drop_left,ite_true]
  change ((NativeByteCodec.fixed count).read ((NativeByteCodec.fixed count).encode raw ++ tail)).map Prod.fst = some raw
  rw [(NativeByteCodec.fixed count).read_encode]
  rfl

def candidate (count : ℕ) : Observation → Option (Fin count → Byte)
  | .start _ => none
  | .output input _ values => if values = [] then none else read count input
  | .hash input _ => read count input

def guesses (count : ℕ) (log : List Observation) : Finset (Fin count → Byte) := (log.filterMap (candidate count)).toFinset

theorem guesses_append (count : ℕ) (first later : List Observation) :
    guesses count (first++later) = guesses count first ∪ guesses count later := by
  simp only [guesses,List.filterMap_append,List.toFinset_append]

theorem read_candidate (count : ℕ) (raw : Fin count → Byte) (tail values : Input) (offset : ℕ) (positive : values ≠ []) :
    candidate count (.output (key (List.ofFn raw ++ tail)) offset values) = some raw := by
  simp only [candidate,positive,ite_false,read_native]

theorem observed_prefix (count : ℕ) (raw : Fin count → Byte) (tail values : Input) (offset : ℕ)
    (log : List Observation) (positive : values ≠ [])
    (present : .output (key (List.ofFn raw ++ tail)) offset values ∈ log) : raw ∈ guesses count log := by
  apply List.mem_toFinset.mpr
  exact List.mem_filterMap.mpr ⟨_,present,read_candidate count raw tail values offset positive⟩

/-- A single known receipt coordinate suffices, at any offset, even through
split or cloned reads. The named raw prefix is kept regardless of its digest. -/
theorem known_prefix (count : ℕ) (raw : Fin count → Byte) (tail : Input) (position : ℕ)
    (log : List Observation) (known : (.inl (key (List.ofFn raw ++ tail),position) : Coordinate) ∈ ObservationReplay.footprint log) :
    raw ∈ guesses count log := by
  obtain ⟨entry,present,coordinate⟩ := Finset.mem_biUnion.mp known
  cases entry with
  | start input => simp [ObservationReplay.coordinates] at coordinate
  | hash input digest => simp [ObservationReplay.coordinates] at coordinate
  | output input offset values =>
    have info := (NativeShakeProjection.output_coordinate input offset values _).mp coordinate
    have inputEq := info.1
    subst input
    have positive : values ≠ [] := by intro empty; simp only [empty,List.length_nil] at info; omega
    exact observed_prefix count raw tail values offset log positive (List.mem_toFinset.mp present)
end
end FormalProof4FHE.HasteBoots.NativeReceiptPrefixView
