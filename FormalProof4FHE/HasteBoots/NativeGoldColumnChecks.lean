module

public import FormalProof4FHE.HasteBoots.NativeGoldArithmetic
public import FormalProof4FHE.HasteBoots.NativeColumnLayout
public import FormalProof4FHE.HasteBoots.NativeBrakedownParameters

@[expose] public section

/-! Raw single-opening coordinate loops. Multiplication and accumulation keep
native lazy u64 representatives; equality compares field values. The array
sizes needed by native indexing are checked separately by the PCS prefix.
Optional getters only totalize this source model outside those preconditions. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldColumnChecks

open NativeFieldRepresentation (GoldWord goldCanonical goldValue)
open NativeFields (Goldilocks)
open NativeBrakedownParameters (Geometry)

def dot (rows block : ℕ) (weights values : List GoldWord) (lane coordinate : ℕ) : GoldWord :=
  NativeGoldArithmetic.sum (List.ofFn (fun row : Fin rows =>
    NativeGoldArithmetic.mul (weights[lane*rows+row.val]?.getD 0) (values[row.val*block+coordinate]?.getD 0)))

def equal (left right : GoldWord) : Bool := decide (goldCanonical left = goldCanonical right)

def coordinate (geometry : Geometry) (random structured test evaluation values : List GoldWord)
    (index lane component : ℕ) : Bool :=
  let address := lane*geometry.stride+index*geometry.blockWidth+component
  equal (dot geometry.rows geometry.blockWidth random values lane component) (test[address]?.getD 0) &&
    equal (dot geometry.rows geometry.blockWidth structured values lane component) (evaluation[address]?.getD 0)

/-- Ascending packing lanes and symbol coordinates, with the native test-first
short circuit inside each coordinate. -/
def check (geometry : Geometry) (width : ℕ) (random structured test evaluation values : List GoldWord)
    (index : ℕ) : Bool :=
  (List.range width).all (fun lane => (List.range geometry.blockWidth).all
    (fun component => coordinate geometry random structured test evaluation values index lane component))

/-- These are the existing checked prefix's array preconditions, not additional
verifier inputs or code/response correctness certificates. -/
def Shape (geometry : Geometry) (width index : ℕ) (random structured test evaluation values : List GoldWord) : Prop :=
  geometry.stride = geometry.blocks*geometry.blockWidth ∧ index < geometry.blocks ∧
    random.length = width*geometry.rows ∧ structured.length = width*geometry.rows ∧
    test.length = width*geometry.stride ∧ evaluation.length = width*geometry.stride ∧
    values.length = geometry.rows*geometry.blockWidth

theorem equal_iff (left right : GoldWord) : equal left right = true ↔ goldValue left = goldValue right := by
  rw [equal,decide_eq_true_eq,← NativeFieldRepresentation.goldValue_eq_iff]

/-- Successful native preconditions put all weight/payload/response accesses
in bounds; the totalization cannot alter an actual checked coordinate. -/
theorem addresses (geometry : Geometry) (width index : ℕ) (random structured test evaluation values : List GoldWord)
    (shape : Shape geometry width index random structured test evaluation values)
    (lane : Fin width) (component : Fin geometry.blockWidth) (row : Fin geometry.rows) :
    lane.val*geometry.rows+row.val < random.length ∧
      lane.val*geometry.rows+row.val < structured.length ∧
      row.val*geometry.blockWidth+component.val < values.length ∧
      lane.val*geometry.stride+index*geometry.blockWidth+component.val < test.length ∧
      lane.val*geometry.stride+index*geometry.blockWidth+component.val < evaluation.length := by
  obtain ⟨stride,bound,rSize,sSize,tSize,eSize,vSize⟩ := shape
  have l := lane.isLt
  have c := component.isLt
  have r := row.isLt
  have weight : lane.val*geometry.rows+row.val < width*geometry.rows := by nlinarith
  have payload : row.val*geometry.blockWidth+component.val < geometry.rows*geometry.blockWidth := by nlinarith
  have response : lane.val*geometry.stride+index*geometry.blockWidth+component.val < width*geometry.stride := by
    have within : index*geometry.blockWidth+component.val < geometry.stride := by rw [stride]; nlinarith
    nlinarith
  exact ⟨by rw [rSize]; exact weight,by rw [sSize]; exact weight,by rw [vSize]; exact payload,
    by rw [tSize]; exact response,by rw [eSize]; exact response⟩

noncomputable section
open scoped BigOperators

def view (words : List GoldWord) (index : ℕ) : Goldilocks := goldValue (words[index]?.getD 0)

theorem dot_value (rows block : ℕ) (weights values : List GoldWord) (lane coordinate : ℕ) :
    goldValue (dot rows block weights values lane coordinate) =
      ∑ row : Fin rows, view weights (lane*rows+row.val)*view values (row.val*block+coordinate) := by
  simp only [dot,NativeGoldArithmetic.sum_value,List.map_ofFn,Function.comp_def,NativeGoldArithmetic.mul_value,List.sum_ofFn,view]

theorem check_iff (geometry : Geometry) (width : ℕ) (random structured test evaluation values : List GoldWord)
    (index : ℕ) : check geometry width random structured test evaluation values index = true ↔
    ∀ lane < width, ∀ component < geometry.blockWidth,
      (∑ row : Fin geometry.rows, view random (lane*geometry.rows+row.val)*view values (row.val*geometry.blockWidth+component)) =
        view test (lane*geometry.stride+index*geometry.blockWidth+component) ∧
      (∑ row : Fin geometry.rows, view structured (lane*geometry.rows+row.val)*view values (row.val*geometry.blockWidth+component)) =
        view evaluation (lane*geometry.stride+index*geometry.blockWidth+component) := by
  simp only [check,List.all_eq_true,List.mem_range,coordinate,Bool.and_eq_true,equal_iff,dot_value,view]

/-- The raw arithmetic gives exactly the existing semantic native-layout dot. -/
theorem dot_layout (width rows block : ℕ) (weights values : List GoldWord)
    (lane : Fin width) (component : Fin block) :
    goldValue (dot rows block weights values lane.val component.val) = NativeColumnLayout.dot
      (fun address : Fin (width*rows) => view weights address.val)
      (fun address : Fin (rows*block) => view values address.val) lane component := by
  rw [dot_value,NativeColumnLayout.dot_eq_sum]
  simp only [NativeColumnLayout.weight_address,NativeColumnLayout.payload_address]

end
end FormalProof4FHE.HasteBoots.NativeGoldColumnChecks
