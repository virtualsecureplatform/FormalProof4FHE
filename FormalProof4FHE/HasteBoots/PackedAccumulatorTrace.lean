module
public import FormalProof4FHE.HasteBoots.AccumulatorEndpointSoundness
public import FormalProof4FHE.HasteBoots.AccumulatorTrace
public import Mathlib.Algebra.Field.ZMod
@[expose] public section

/-! Canonical coefficient-array packing and reference meaning of the complete
accumulator constraint family. Base coefficients may be embedded into an
analysis extension field. Original decomposition sources remain independent
parameters. Native array/field/heap correspondence is a separate refinement. -/
namespace FormalProof4FHE.HasteBoots.PackedAccumulatorTrace
open OracleSpec OracleComp
open NativeBlindRotation (Cipher Control)
noncomputable section

structure Rounds (r : ℕ) where
  count : ℕ
  positive : 0 < count
  fits : count ≤ 2^r

def Rounds.shape {r : ℕ} (rounds : Rounds r) : AccumulatorTrace.Shape :=
  ⟨rounds.count,2^r,rounds.positive,rounds.fits⟩

/-- Native contiguous polynomial addresses: lane + width*coefficient cell. -/
def polynomial (c lanes : ℕ) : (MatrixFold.Cube c × Fin (2^lanes)) ≃ Fin (2^(c+lanes)) :=
  (Equiv.prodCongr (FlatMatrixFold.index c) (Equiv.refl _)).trans
    (finProdFinEquiv.trans (finCongr (Nat.pow_add 2 c lanes).symm))

theorem polynomial_val (c lanes : ℕ) (cell : MatrixFold.Cube c) (lane : Fin (2^lanes)) :
    (polynomial c lanes (cell,lane)).val = lane.val+2^lanes*(FlatMatrixFold.index c cell).val := rfl

theorem scalar_address {c lanes r : ℕ} (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r)
    (half : Bool) (lane : Fin (2^lanes)) :
    2^lanes*(FlatMatrixFold.index ((1+r)+c) (AccumulatorPackedQueries.coordinate cell row half)).val+lane.val =
      (polynomial c lanes (cell,lane)).val+2^(c+lanes)*((FlatMatrixFold.index r row).val+2^r*(if half then 1 else 0)) := by
  rw [polynomial_val, AccumulatorPackedQueries.coordinate_index, pow_add]
  ring

variable {q c lanes r : ℕ} [Fact q.Prime] {F : Type} [Field F]

def pack (embed : ZMod q →+* F) (rows : Fin (2^r) → Cipher q (2^(c+lanes))) :
    AccumulatorMatrixSoundness.Table F (2^lanes) c r :=
  fun position lane =>
    let p := AccumulatorQuerySplit.coordinates c r position
    embed (rows (FlatMatrixFold.index r p.2.1) p.2.2 (polynomial c lanes (p.1,lane)))

def endpoint (embed : ZMod q →+* F) (value : Cipher q (2^(c+lanes))) :
    Bool → MatrixFold.Cube c → Fin (2^lanes) → F :=
  fun half cell lane => embed (value half (polynomial c lanes (cell,lane)))

theorem pack_coordinate (embed : ZMod q →+* F) (rows : Fin (2^r) → Cipher q (2^(c+lanes)))
    (cell : MatrixFold.Cube c) (row : MatrixFold.Cube r) (half : Bool) (lane : Fin (2^lanes)) :
    pack embed rows (AccumulatorPackedQueries.coordinate cell row half) lane =
      embed (rows (FlatMatrixFold.index r row) half (polynomial c lanes (cell,lane))) := by
  simp only [pack, AccumulatorQuerySplit.coordinates_apply]

theorem pack_injective (embed : ZMod q →+* F) : Function.Injective (pack (c := c) (lanes := lanes) (r := r) embed) := by
  intro first last equal
  funext row half index
  obtain ⟨⟨cell,lane⟩,coefficient⟩ := (polynomial c lanes).surjective index
  obtain ⟨rowCell,address⟩ := (FlatMatrixFold.index r).surjective row
  apply embed.injective
  have values := congrFun (congrFun equal (AccumulatorPackedQueries.coordinate cell rowCell half)) lane
  simpa only [pack_coordinate, address, coefficient] using values

theorem pack_sub (embed : ZMod q →+* F) (first last : Fin (2^r) → Cipher q (2^(c+lanes))) :
    pack embed (first-last) = pack embed first-pack embed last := by
  funext position lane
  exact map_sub embed _ _

theorem pack_add (embed : ZMod q →+* F) (first last : Fin (2^r) → Cipher q (2^(c+lanes))) :
    pack embed (first+last) = pack embed first+pack embed last := by
  funext position lane
  exact map_add embed _ _

/-- The five accumulator arrays are packed canonically. The two original
decomposition tables are retained as supplied, rather than replaced by copies. -/
def sources (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r) :
    AccumulatorMatrixSoundness.Sources F (2^lanes) c r where
  input := pack embed tables.input
  product := pack embed tables.product
  difference := pack embed tables.difference
  external := pack embed tables.external
  output := pack embed tables.output
  duplicateA := decompositionA
  duplicateB := decompositionB
  initial := endpoint embed initial
  final := endpoint embed final
  start := (FlatMatrixFold.index r).symm (AccumulatorTrace.wrap rounds.shape)
  finish := (FlatMatrixFold.index r).symm (AccumulatorTrace.last rounds.shape)

/-- Every original row and every polynomial coefficient is retained. -/
theorem arithmetic_of_holds (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (holds : AccumulatorEndpointSoundness.FullHolds (sources embed rounds tables initial final decompositionA decompositionB)) :
    AccumulatorTrace.Arithmetic tables := by
  have subtraction := holds.1 (0 : Fin 5)
  change pack embed tables.difference-(pack embed tables.product-pack embed tables.input) = 0 at subtraction
  have subeq := (sub_eq_zero.mp subtraction).trans (pack_sub embed tables.product tables.input).symm
  have baseSub := pack_injective embed subeq
  have addition := holds.1 (1 : Fin 5)
  change pack embed tables.output-(pack embed tables.input+pack embed tables.external) = 0 at addition
  have addeq := (sub_eq_zero.mp addition).trans (pack_add embed tables.input tables.external).symm
  have baseAdd := pack_injective embed addeq
  exact ⟨fun row => congrFun baseSub row,fun row => congrFun baseAdd row⟩

theorem zero_index (r : ℕ) : (FlatMatrixFold.index r (AccumulatorShiftQueries.zero r)).val = 0 := by
  induction r with
  | zero =>
    have bound := (FlatMatrixFold.index 0 (AccumulatorShiftQueries.zero 0)).isLt
    change _ < 1 at bound
    omega
  | succ r ih =>
    change (FlatMatrixFold.index (r+1) (false,AccumulatorShiftQueries.zero r)).val = 0
    rw [FlatMatrixFold.index_succ_val]
    simp only [Bool.false_eq_true, ↓reduceIte, ih]

theorem next_index (rounds : Rounds r) (row : MatrixFold.Cube r) :
    FlatMatrixFold.index r (AccumulatorShiftQueries.successor row) =
      AccumulatorTrace.next rounds.shape (FlatMatrixFold.index r row) := by
  apply Fin.ext
  exact AccumulatorShiftQueries.successor_index row

theorem slice_pack (embed : ZMod q →+* F) (rows : Fin (2^r) → Cipher q (2^(c+lanes))) (target : MatrixFold.Cube r) :
    AccumulatorEndpointSoundness.slice (pack embed rows) target =
      AccumulatorEndpointSoundness.publicTable (endpoint embed (rows (FlatMatrixFold.index r target))) := by
  funext position lane
  unfold AccumulatorEndpointSoundness.slice AccumulatorEndpointSoundness.publicTable
  rw [pack_coordinate]
  rfl

theorem public_injective (embed : ZMod q →+* F) :
    Function.Injective (fun value : Cipher q (2^(c+lanes)) => AccumulatorEndpointSoundness.publicTable (endpoint embed value)) := by
  intro first last equal
  funext half index
  obtain ⟨⟨cell,lane⟩,coefficient⟩ := (polynomial c lanes).surjective index
  apply embed.injective
  have values := congrFun (congrFun equal (MonomialBitOrder.append cell (show MatrixFold.Cube 1 from (half,())))) lane
  simpa only [AccumulatorEndpointSoundness.publicTable_append, endpoint, coefficient] using values

theorem endpoints_of_holds (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (holds : AccumulatorEndpointSoundness.FullHolds (sources embed rounds tables initial final decompositionA decompositionB)) :
    tables.input (AccumulatorTrace.first rounds.shape) = initial ∧ tables.output (AccumulatorTrace.last rounds.shape) = final := by
  have first := holds.2 false
  change AccumulatorEndpointSoundness.slice (pack embed tables.input) (AccumulatorShiftQueries.zero r)-
    AccumulatorEndpointSoundness.publicTable (endpoint embed initial) = 0 at first
  have initialEq := public_injective embed ((slice_pack embed tables.input (AccumulatorShiftQueries.zero r)).symm.trans (sub_eq_zero.mp first))
  have firstIndex : FlatMatrixFold.index r (AccumulatorShiftQueries.zero r) = AccumulatorTrace.first rounds.shape :=
    Fin.ext (zero_index r)
  have last := holds.2 true
  change AccumulatorEndpointSoundness.slice (pack embed tables.output) ((FlatMatrixFold.index r).symm (AccumulatorTrace.last rounds.shape))-
    AccumulatorEndpointSoundness.publicTable (endpoint embed final) = 0 at last
  have finalEq := public_injective embed ((slice_pack embed tables.output _).symm.trans (sub_eq_zero.mp last))
  constructor
  · simpa only [firstIndex] using initialEq
  · have lastIndex := (FlatMatrixFold.index r).apply_symm_apply (AccumulatorTrace.last rounds.shape)
    exact (congrArg tables.output lastIndex).symm.trans finalEq

theorem advance_pack (embed : ZMod q →+* F) (rounds : Rounds r)
    (rows : Fin (2^r) → Cipher q (2^(c+lanes))) :
    AccumulatorMatrixSoundness.advance (pack embed rows) =
      pack embed (fun row => rows (AccumulatorTrace.next rounds.shape row)) := by
  funext position lane
  simp only [AccumulatorMatrixSoundness.advance, pack_coordinate, pack, next_index rounds]

theorem boundary_pack (embed : ZMod q →+* F) (target : MatrixFold.Cube r) (value : Cipher q (2^(c+lanes))) :
    AccumulatorMatrixSoundness.boundary target (endpoint embed value) =
      pack embed (fun row => if row = FlatMatrixFold.index r target then value else 0) := by
  funext position lane
  by_cases same : FlatMatrixFold.index r (AccumulatorQuerySplit.coordinates c r position).2.1 = FlatMatrixFold.index r target
  · simp only [AccumulatorMatrixSoundness.boundary, endpoint, pack, AccumulatorPackedQueries.impulse, ite_eq_left same]
  · simp only [AccumulatorMatrixSoundness.boundary, pack, AccumulatorPackedQueries.impulse, ite_eq_right same,
      Pi.zero_apply, map_zero]

theorem boundary_index (embed : ZMod q →+* F) (target : Fin (2^r)) (value : Cipher q (2^(c+lanes))) :
    AccumulatorMatrixSoundness.boundary ((FlatMatrixFold.index r).symm target) (endpoint embed value) =
      pack embed (fun row => if row = target then value else 0) := by
  exact (boundary_pack embed _ value).trans
    (congrArg (fun index : Fin (2^r) => pack embed (fun row => if row = index then value else 0))
      ((FlatMatrixFold.index r).apply_symm_apply target))

theorem cyclic_of_holds (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (holds : AccumulatorEndpointSoundness.FullHolds (sources embed rounds tables initial final decompositionA decompositionB)) :
    ∀ row, tables.input (AccumulatorTrace.next rounds.shape row)-tables.output row =
      (if row = AccumulatorTrace.wrap rounds.shape then initial else 0)-
      (if row = AccumulatorTrace.last rounds.shape then final else 0) := by
  have zero := holds.1 (4 : Fin 5)
  change AccumulatorMatrixSoundness.advance (pack embed tables.input)-pack embed tables.output-
    (AccumulatorMatrixSoundness.boundary ((FlatMatrixFold.index r).symm (AccumulatorTrace.wrap rounds.shape)) (endpoint embed initial)-
      AccumulatorMatrixSoundness.boundary ((FlatMatrixFold.index r).symm (AccumulatorTrace.last rounds.shape)) (endpoint embed final)) = 0 at zero
  let moved : Fin (2^r) → Cipher q (2^(c+lanes)) := fun row => tables.input (AccumulatorTrace.next rounds.shape row)
  let wrapRow : Fin (2^r) := AccumulatorTrace.wrap rounds.shape
  let finalRow : Fin (2^r) := AccumulatorTrace.last rounds.shape
  let firstRows : Fin (2^r) → Cipher q (2^(c+lanes)) := fun row => if row = wrapRow then initial else 0
  let lastRows : Fin (2^r) → Cipher q (2^(c+lanes)) := fun row => if row = finalRow then final else 0
  have left : pack embed (moved-tables.output) = AccumulatorMatrixSoundness.advance (pack embed tables.input)-pack embed tables.output :=
    (pack_sub embed moved tables.output).trans
      (congrArg (fun value : AccumulatorMatrixSoundness.Table F (2^lanes) c r => value-pack embed tables.output)
        (advance_pack embed rounds tables.input).symm)
  have right : pack embed (firstRows-lastRows) =
      AccumulatorMatrixSoundness.boundary ((FlatMatrixFold.index r).symm (AccumulatorTrace.wrap rounds.shape)) (endpoint embed initial)-
      AccumulatorMatrixSoundness.boundary ((FlatMatrixFold.index r).symm (AccumulatorTrace.last rounds.shape)) (endpoint embed final) :=
    (pack_sub embed firstRows lastRows).trans
      (congrArg₂ (fun (first last : AccumulatorMatrixSoundness.Table F (2^lanes) c r) => first-last)
        (boundary_index embed wrapRow initial).symm
        (boundary_index embed finalRow final).symm)
  have base := pack_injective embed (left.trans ((sub_eq_zero.mp zero).trans right.symm))
  exact fun row => congrFun base row

theorem linkage_of_holds (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (holds : AccumulatorEndpointSoundness.FullHolds (sources embed rounds tables initial final decompositionA decompositionB)) :
    AccumulatorTrace.Linkage rounds.shape tables initial final :=
  ⟨(endpoints_of_holds embed rounds tables initial final decompositionA decompositionB holds).1,
    (endpoints_of_holds embed rounds tables initial final decompositionA decompositionB holds).2,
    cyclic_of_holds embed rounds tables initial final decompositionA decompositionB holds⟩

variable {levels : ℕ}

theorem validTrace (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (holds : AccumulatorEndpointSoundness.FullHolds (sources embed rounds tables initial final decompositionA decompositionB))
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (rotation : ∀ round, tables.product (AccumulatorTrace.active rounds.shape round) = fun half =>
      NativeBlindRotation.rotate (controls round).2 (tables.input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, tables.external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1 (tables.difference (AccumulatorTrace.active rounds.shape round))) :
    NativeBlindRotation.ValidTrace bits (List.ofFn controls) initial (List.ofFn (AccumulatorTrace.traceAt rounds.shape tables)) final :=
  AccumulatorTrace.validTrace_tables rounds.shape tables initial final
    (arithmetic_of_holds embed rounds tables initial final decompositionA decompositionB holds)
    (linkage_of_holds embed rounds tables initial final decompositionA decompositionB holds) bits controls rotation external

theorem output_eq_run (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (holds : AccumulatorEndpointSoundness.FullHolds (sources embed rounds tables initial final decompositionA decompositionB))
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (rotation : ∀ round, tables.product (AccumulatorTrace.active rounds.shape round) = fun half =>
      NativeBlindRotation.rotate (controls round).2 (tables.input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, tables.external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1 (tables.difference (AccumulatorTrace.active rounds.shape round))) :
    final = NativeBlindRotation.run bits (List.ofFn controls) initial :=
  NativeBlindRotation.validTrace_output bits _ _ _ _
    (validTrace embed rounds tables initial final decompositionA decompositionB holds bits controls rotation external)

variable [Fintype F] [DecidableEq F] [SampleableType (Fin (2^lanes) → F)]

/-- A wrong reference accumulator with truthful multiplication-stage identities
passes the fresh accumulator arithmetic checks only within their proved bound.
Source authentication and native Fiat--Shamir freshness are not asserted. -/
theorem wrong_output_bound (nodes : PackedSumcheckRound.Node (2^lanes) ↪ F)
    (embed : ZMod q →+* F) (rounds : Rounds r)
    (tables : AccumulatorTrace.Tables q (2^(c+lanes)) (2^r)) (initial final : Cipher q (2^(c+lanes)))
    (decompositionA decompositionB : AccumulatorMatrixSoundness.Table F (2^lanes) c r)
    (bits : ℕ) (controls : Fin rounds.count → Control q (2^(c+lanes)) levels × ℕ)
    (rotation : ∀ round, tables.product (AccumulatorTrace.active rounds.shape round) = fun half =>
      NativeBlindRotation.rotate (controls round).2 (tables.input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, tables.external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1 (tables.difference (AccumulatorTrace.active rounds.shape round)))
    (wrong : final ≠ NativeBlindRotation.run bits (List.ofFn controls) initial) :
    Pr{let query ← MatrixCompression.sample nodes ((1+r)+c)}[
      AccumulatorEndpointSoundness.FullCheck (sources embed rounds tables initial final decompositionA decompositionB) query] ≤
      ((((1+r)+c : ℕ) : ENNReal) * (((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card F)^(2^lanes)))) := by
  apply AccumulatorEndpointSoundness.fresh_full_bound nodes
  intro holds
  exact wrong (output_eq_run embed rounds tables initial final decompositionA decompositionB holds bits controls rotation external)

end
end FormalProof4FHE.HasteBoots.PackedAccumulatorTrace
