module

public import FormalProof4FHE.HasteBoots.BatchGrouping
public import FormalProof4FHE.HasteBoots.NativeGoldPcsWire
@[expose] public section

/-! Native Brakedown response grouping by the exact ordered left query prefix.
Goldilocks equality reduces every entry modulo the field while the original
raw query remains available for transcript serialization. Native binding and
shape gates precede use of these keys; total `take` is not a decoder or a
replacement for those gates. Rust equality/instruction refinement remains open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldQueryGroups
open NativeGoldPcsWire (Matrix Pair Query)
open NativeFieldRepresentation (GoldWord goldCanonical goldValue)
open NativeFields (Goldilocks)
open NativePrefixCodec (Vector)

abbrev MatrixKey := ℕ × List ℕ
abbrev PairKey := MatrixKey × MatrixKey
abbrev Key := List PairKey

/-- Canonical representatives are used only for equality; original transcript bytes are retained. -/
def matrixKey (matrix : Matrix) : MatrixKey := (matrix.width.val,matrix.values.val.map goldCanonical)
def pairKey (pair : Pair) : PairKey := (matrixKey pair.1,matrixKey pair.2)
/-- Keep the exact ordered prefix, not its tensor weights or an unordered set of matrices. -/
def key (left : ℕ) (query : Query) : Key := (query.val.take left).map pairKey
def keys (left : ℕ) (queries : Vector Query) : List Key := queries.val.map (key left)

abbrev groupCount (left : ℕ) (queries : Vector Query) := (BatchGrouping.compute (keys left queries)).1.length

def position (left : ℕ) (queries : Vector Query) (index : Fin queries.val.length) : Fin (keys left queries).length :=
  ⟨index.val,by simpa only [keys,List.length_map] using index.isLt⟩

def group (left : ℕ) (queries : Vector Query) (index : Fin queries.val.length) : Fin (groupCount left queries) :=
  BatchGrouping.groupOf (keys left queries) (position left queries index)

def representative (left : ℕ) (queries : Vector Query) (index : Fin (groupCount left queries)) : Fin queries.val.length :=
  let selected := BatchGrouping.representative (keys left queries) index
  ⟨selected.val,by simpa only [keys,List.length_map] using selected.isLt⟩

def MatrixEqual (left right : Matrix) : Prop :=
  left.width = right.width ∧ left.values.val.map goldValue = right.values.val.map goldValue

def PairEqual (left right : Pair) : Prop := MatrixEqual left.1 right.1 ∧ MatrixEqual left.2 right.2

theorem canonical_eq_iff (left right : List GoldWord) :
    left.map goldCanonical = right.map goldCanonical ↔ left.map goldValue = right.map goldValue := by
  constructor
  · intro same
    have cast := congrArg (List.map (fun value : ℕ => (value : Goldilocks))) same
    simpa only [List.map_map,Function.comp_def,NativeFieldRepresentation.goldCanonical_cast] using cast
  · intro same
    have canonical := congrArg (List.map (fun value : Goldilocks => value.val)) same
    simpa only [List.map_map,Function.comp_def,NativeFieldRepresentation.goldValue_val] using canonical

theorem matrixKey_eq_iff (left right : Matrix) : matrixKey left = matrixKey right ↔ MatrixEqual left right := by
  simp only [matrixKey,Prod.mk.injEq,MatrixEqual,canonical_eq_iff,Fin.val_inj]

theorem pairKey_eq_iff (left right : Pair) : pairKey left = pairKey right ↔ PairEqual left right := by
  simp only [pairKey,Prod.mk.injEq,matrixKey_eq_iff,PairEqual]

private theorem map_pairKey_eq_iff (left right : List Pair) :
    left.map pairKey = right.map pairKey ↔ List.Forall₂ PairEqual left right := by
  induction left generalizing right with
  | nil => cases right <;> simp
  | cons first rest ih => cases right <;> simp [pairKey_eq_iff,ih]

/-- Exactly the ordered native matrix comparison, modulo base-field representatives at every entry. -/
theorem key_eq_iff (left : ℕ) (first second : Query) : key left first = key left second ↔
    List.Forall₂ PairEqual (first.val.take left) (second.val.take left) :=
  map_pairKey_eq_iff _ _

theorem group_eq_iff (left : ℕ) (queries : Vector Query) (first second : Fin queries.val.length) :
    group left queries first = group left queries second ↔
      List.Forall₂ PairEqual ((queries.val.get first).val.take left) ((queries.val.get second).val.take left) := by
  have compared := BatchGrouping.groupOf_eq_iff (keys left queries) (position left queries first) (position left queries second)
  have at_index (index : Fin queries.val.length) : (keys left queries).get (position left queries index) = key left (queries.val.get index) := by
    simp only [keys,List.get_eq_getElem,List.getElem_map,position]
  rw [at_index first,at_index second] at compared
  exact compared.trans (key_eq_iff left (queries.val.get first) (queries.val.get second))

theorem representative_key (left : ℕ) (queries : Vector Query) (index : Fin (groupCount left queries)) :
    key left (queries.val.get (representative left queries index)) = (BatchGrouping.compute (keys left queries)).1.get index := by
  have selected := BatchGrouping.representative_key (keys left queries) index
  simpa only [keys,List.get_eq_getElem,List.getElem_map,representative] using selected

theorem representative_first (left : ℕ) (queries : Vector Query) (index : Fin (groupCount left queries))
    (earlier : Fin queries.val.length) (before : earlier.val < (representative left queries index).val) :
    ¬List.Forall₂ PairEqual ((queries.val.get earlier).val.take left)
      ((queries.val.get (representative left queries index)).val.take left) := by
  rw [← key_eq_iff,representative_key]
  have absent := BatchGrouping.representative_first (keys left queries) index (position left queries earlier) before
  simpa only [keys,List.get_eq_getElem,List.getElem_map,position] using absent

/-- Every original claim finishes against the response for its computed prefix group. -/
theorem group_key (left : ℕ) (queries : Vector Query) (index : Fin queries.val.length) :
    (BatchGrouping.compute (keys left queries)).1.get (group left queries index) = key left (queries.val.get index) := by
  have selected := BatchGrouping.group_key (keys left queries) (position left queries index)
  simpa only [group,keys,List.get_eq_getElem,List.getElem_map,position] using selected
end FormalProof4FHE.HasteBoots.NativeGoldQueryGroups
