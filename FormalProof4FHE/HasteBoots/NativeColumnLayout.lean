module

public import FormalProof4FHE.HasteBoots.MatrixOpeningSecurity
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Zip

@[expose] public section

/-!
# Native sampled-column addresses and coordinate checks

Packing width and code-symbol width are separate dimensions. Payloads read
row*block+coordinate, weights read lane*rows+row, and encoded responses read
lane*(length*block)+position*block+coordinate. The literal left fold of products
is the row combination used by matrix-opening soundness. Pairing proof columns
with sampled indices and checking every received column transports through
sorting/deduplication to every original ordered draw.
This is typed array/loop semantics; Rust memory and field implementation
refinement and native NTT encoding remain separate obligations.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NativeColumnLayout

variable {F Digest : Type} {width rows block length leftCount height queries : ℕ}

def weightAddress (lane : Fin width) (row : Fin rows) : Fin (width * rows) :=
  finProdFinEquiv (lane, row)

def payloadAddress (row : Fin rows) (coordinate : Fin block) : Fin (rows * block) :=
  finProdFinEquiv (row, coordinate)

def responseAddress (lane : Fin width) (position : Fin length) (coordinate : Fin block) :
    Fin (width * (length * block)) :=
  finProdFinEquiv (lane, finProdFinEquiv (position, coordinate))

theorem weight_address (lane : Fin width) (row : Fin rows) :
    (weightAddress lane row).val = lane.val * rows + row.val := RowLayout.address lane row

theorem payload_address (row : Fin rows) (coordinate : Fin block) :
    (payloadAddress row coordinate).val = row.val * block + coordinate.val := RowLayout.address row coordinate

theorem response_address (lane : Fin width) (position : Fin length) (coordinate : Fin block) :
    (responseAddress lane position coordinate).val =
      lane.val * (length * block) + position.val * block + coordinate.val := by
  rw [responseAddress, RowLayout.address, RowLayout.address]
  exact (Nat.add_assoc _ _ _).symm

/-- The fields remaining after a raw column has passed its dimension checks. -/
structure Data (F Digest : Type) (height rows block : ℕ) where
  values : Fin (rows * block) → F
  leaf : Digest
  siblings : List.Vector Digest height

structure Column (F Digest : Type) (height rows block : ℕ) extends Data F Digest height rows block where
  position : Fin (2 ^ height)

/-- Native zip assigns each proof column the verifier's sampled position. -/
def attach (indices : List (Fin (2 ^ height))) (proofs : List (Data F Digest height rows block)) :
    List (Column F Digest height rows block) :=
  (indices.zip proofs).map fun pair =>
    { position := pair.1, values := pair.2.values, leaf := pair.2.leaf, siblings := pair.2.siblings }

theorem positions_attach (indices : List (Fin (2 ^ height))) (proofs : List (Data F Digest height rows block))
    (sameLength : indices.length = proofs.length) :
    (attach indices proofs).map Column.position = indices := by
  simp only [attach, List.map_map]
  exact List.map_fst_zip sameLength.le

/-- Coverage is stated on the original with-replacement draws. -/
def Covers (columns : List (Column F Digest height rows block)) (draw : Fin queries → Fin (2 ^ height)) : Prop :=
  ∀ i, ∃ column ∈ columns, column.position = draw i

/-- Membership-level interpretation of native sorting followed by deduplication. -/
def distinctIndices (draw : Fin queries → Fin (2 ^ height)) : List (Fin (2 ^ height)) :=
  ((List.ofFn draw).mergeSort (fun a b => decide (a ≤ b))).dedup

theorem mem_distinctIndices (draw : Fin queries → Fin (2 ^ height)) (i : Fin queries) :
    draw i ∈ distinctIndices draw := by
  simp only [distinctIndices, List.mem_dedup, List.mem_mergeSort, List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem covers_attach (draw : Fin queries → Fin (2 ^ height))
    (indices : List (Fin (2 ^ height))) (proofs : List (Data F Digest height rows block))
    (sameLength : indices.length = proofs.length) (present : ∀ i, draw i ∈ indices) :
    Covers (attach indices proofs) draw := by
  intro i
  have member : draw i ∈ (attach indices proofs).map Column.position := by
    rw [positions_attach indices proofs sameLength]
    exact present i
  exact List.mem_map.mp member

theorem covers_distinct_attach (draw : Fin queries → Fin (2 ^ height))
    (proofs : List (Data F Digest height rows block))
    (sameLength : (distinctIndices draw).length = proofs.length) :
    Covers (attach (distinctIndices draw) proofs) draw :=
  covers_attach draw _ proofs sameLength (mem_distinctIndices draw)

section Field

variable [Field F]

/-- Native sum of row products, accumulated from left to right starting at zero. -/
def dot (weights : Fin (width * rows) → F) (values : Fin (rows * block) → F)
    (lane : Fin width) (coordinate : Fin block) : F :=
  (List.ofFn (fun row : Fin rows => weights (weightAddress lane row) *
    values (payloadAddress row coordinate))).foldl (· + ·) 0

theorem dot_eq_sum (weights : Fin (width * rows) → F) (values : Fin (rows * block) → F)
    (lane : Fin width) (coordinate : Fin block) :
    dot weights values lane coordinate =
      ∑ row, weights (weightAddress lane row) * values (payloadAddress row coordinate) := by
  rw [dot, ← List.sum_eq_foldl, List.sum_ofFn]

def expandedWeights (weights : Fin (width * (leftCount * width)) → F)
    (lane : Fin width) (row : Fin leftCount × Fin width) : F :=
  weights (weightAddress lane (finProdFinEquiv row))

def expandedWord (word : Fin length → Fin ((leftCount * width) * block) → F)
    (position : Fin length) (row : Fin leftCount × Fin width) (coordinate : Fin block) : F :=
  word position (payloadAddress (finProdFinEquiv row) coordinate)

def expandedResponse (response : Fin (width * (length * block)) → F)
    (lane : Fin width) (position : Fin length) (coordinate : Fin block) : F :=
  response (responseAddress lane position coordinate)


/-- Native whole-column payload before field/byte serialization. -/
def packPayload {n : ℕ} (values : Fin n → F) : List F := List.ofFn values

/-- Total typed interpretation, with zero at absent coordinates. Authenticated
well-sized payloads recover exactly; arbitrary frozen lists remain total. -/
def unpackPayload (n : ℕ) (values : List F) (index : Fin n) : F :=
  values[index.val]?.getD 0

theorem unpack_packPayload {n : ℕ} (values : Fin n → F) :
    unpackPayload n (packPayload values) = values := by
  funext index
  simp [unpackPayload, packPayload]

def flattenWeights (weights : Fin width → (Fin leftCount × Fin width) → F)
    (index : Fin (width * (leftCount * width))) : F :=
  let pair := finProdFinEquiv.symm index
  weights pair.1 (finProdFinEquiv.symm pair.2)

omit [Field F] in
theorem expanded_flattenWeights (weights : Fin width → (Fin leftCount × Fin width) → F) :
    expandedWeights (flattenWeights weights) = weights := by
  funext lane row
  simp [expandedWeights, flattenWeights, weightAddress]

def flattenResponse (response : Fin width → Fin length → Fin block → F)
    (index : Fin (width * (length * block))) : F :=
  let outer := finProdFinEquiv.symm index
  let inner := finProdFinEquiv.symm outer.2
  response outer.1 inner.1 inner.2

omit [Field F] in
theorem expanded_flattenResponse (response : Fin width → Fin length → Fin block → F) :
    expandedResponse (flattenResponse response) = response := by
  funext lane position coordinate
  simp [expandedResponse, flattenResponse, responseAddress]

/-- The native row fold is the semantic whole-column linear combination. -/
theorem dot_eq_combine (weights : Fin (width * (leftCount * width)) → F)
    (word : Fin length → Fin ((leftCount * width) * block) → F)
    (position : Fin length) (lane : Fin width) (coordinate : Fin block) :
    dot weights (word position) lane coordinate =
      StructuredOpening.combine (expandedWeights weights lane) (expandedWord word) position coordinate := by
  classical
  rw [dot_eq_sum]
  simp only [StructuredOpening.combine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    expandedWeights, expandedWord]
  exact (finProdFinEquiv.sum_comp (fun row : Fin (leftCount * width) =>
    weights (weightAddress lane row) * word position (payloadAddress row coordinate))).symm

/-- Native nested lane/coordinate checks on all paired sampled columns. -/
def Checks (columns : List (Column F Digest height rows block))
    (weights : Fin (width * rows) → F) (response : Fin (width * ((2 ^ height) * block)) → F) : Prop :=
  ∀ column ∈ columns, ∀ lane coordinate,
    dot weights column.values lane coordinate = response (responseAddress lane column.position coordinate)

/-- Pure coordinate part of native acceptance: every lane/coordinate checks
both response families on the same received whole column. -/
def allCoordinates [DecidableEq F] (columns : List (Column F Digest height rows block))
    (testWeights structuredWeights : Fin (width * rows) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F) : Bool :=
  columns.all fun column =>
    (List.ofFn fun lane : Fin width =>
      (List.ofFn fun coordinate : Fin block =>
        decide (dot testWeights column.values lane coordinate =
          testResponse (responseAddress lane column.position coordinate)) &&
        decide (dot structuredWeights column.values lane coordinate =
          structuredResponse (responseAddress lane column.position coordinate))).all id).all id

theorem allCoordinates_eq_true_iff [DecidableEq F]
    (columns : List (Column F Digest height rows block))
    (testWeights structuredWeights : Fin (width * rows) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F) :
    allCoordinates columns testWeights structuredWeights testResponse structuredResponse = true ↔
      Checks columns testWeights testResponse ∧ Checks columns structuredWeights structuredResponse := by
  simp [allCoordinates, Checks, List.mem_ofFn, List.all_eq_true, forall_and]

/-- Once authentication supplies the same fixed payload at each received
position, every ordered draw satisfies the semantic response check. -/
theorem agrees_of_checks
    (columns : List (Column F Digest height (leftCount * width) block))
    (draw : Fin queries → Fin (2 ^ height)) (covered : Covers columns draw)
    (word : Fin (2 ^ height) → Fin ((leftCount * width) * block) → F)
    (values : ∀ column ∈ columns, column.values = word column.position)
    (weights : Fin (width * (leftCount * width)) → F)
    (response : Fin (width * ((2 ^ height) * block)) → F)
    (checked : Checks columns weights response) :
    ∀ lane, ColumnOpening.Agrees (StructuredOpening.combine (expandedWeights weights lane) (expandedWord word))
      (expandedResponse response lane) draw := by
  classical
  intro lane i
  obtain ⟨column, member, position⟩ := covered i
  funext coordinate
  have same := checked column member lane coordinate
  rw [values column member, position] at same
  exact (dot_eq_combine weights word (draw i) lane coordinate).symm.trans same

end Field

end FormalProof4FHE.HasteBoots.NativeColumnLayout
