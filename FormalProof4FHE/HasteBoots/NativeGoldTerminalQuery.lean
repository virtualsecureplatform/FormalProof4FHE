module

public import FormalProof4FHE.HasteBoots.NativeGoldTerminalArithmetic
public import FormalProof4FHE.HasteBoots.NativeGoldScalarQueryMeaning

@[expose] public section

/-!
# Literal lookup-terminal source query/application fold

Each actually zipped source vector is post-mapped and padding-checked before
its weighted raw extension product is added. Unmatched tails are never
projected. Only after this complete fold does the native prefix/residual
stage execute. The acceptance observation is `some true`; projection/domain
failure and unequal terminal value remain distinct outcomes in this model.
PCS authentication and instruction/scheduler refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldTerminalQuery

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldCoefficientsQuery (Query)
open NativeUsizeMessage (Usize)

def compressFrom (width : ℕ) (query : Query) : List (List GoldWord × Word) → Word → Option Word
  | [], out => some out
  | (input, weight) :: tail, out => (NativeGoldPostMap.project width query.post input).bind (fun source =>
      compressFrom width query tail (NativeGoldExtensionArithmetic.add out (NativeGoldCubic.mul weight source)))

def compress (width : ℕ) (query : Query) (sources : List (List GoldWord)) (powers : List Word) : Option Word :=
  compressFrom width query (sources.zip powers) NativeGoldLookup.zero

def value (width : ℕ) (query : Query) (eqPoint point : List Word) (count : Usize)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper : Word) : Option Word :=
  (compress width query sources powers).bind (fun source =>
    (NativeGoldTerminalArithmetic.prefixValue point count).map (fun mask =>
      NativeGoldCubic.mul (NativeGoldTerminalArithmetic.equality eqPoint point)
        (NativeGoldTerminalArithmetic.residual r mask source helper)))

def check (width : ℕ) (query : Query) (eqPoint point : List Word) (count : Usize)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper expected : Word) : Option Bool :=
  (value width query eqPoint point count r sources powers helper).map
    (fun out => NativeGoldInterpolation.equal out expected)

/-- The caller constructs its actual pulled query before the terminal guard. -/
def constructedCheck (sourceVars width : ℕ) (eqPoint point : List Word) (count : Usize)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper expected : Word) : Option Bool :=
  (NativeGoldScalarQuery.scalarQuery sourceVars width point).bind
    (fun query => check width query eqPoint point count r sources powers helper expected)

theorem compress_no_sources (width : ℕ) (query : Query) (powers : List Word) :
    compress width query [] powers = some NativeGoldLookup.zero := rfl

theorem compress_no_powers (width : ℕ) (query : Query) (sources : List (List GoldWord)) :
    compress width query sources [] = some NativeGoldLookup.zero := by
  simp only [compress, List.zip_nil_right, compressFrom]

/-- Even zero weights do not bypass the original used vector's checks. -/
theorem compressFrom_head_failure (width : ℕ) (query : Query) (input : List GoldWord)
    (weight out : Word) (tail : List (List GoldWord × Word))
    (failed : NativeGoldPostMap.project width query.post input = none) :
    compressFrom width query ((input, weight) :: tail) out = none := by
  rw [compressFrom, failed, Option.bind_none]

theorem compress_take_min (width : ℕ) (query : Query) (sources : List (List GoldWord)) (powers : List Word) :
    compress width query sources powers = compress width query
      (sources.take (min sources.length powers.length)) (powers.take (min sources.length powers.length)) := by
  unfold compress
  rw [← List.zip_eq_zip_take_min]

/-- Arbitrary unmatched source tails, including malformed vectors, are ignored. -/
theorem compress_append_sources (width : ℕ) (query : Query) (sources extra : List (List GoldWord)) (powers : List Word)
    (length : sources.length = powers.length) :
    compress width query (sources ++ extra) powers = compress width query sources powers := by
  have same : (sources ++ extra).zip powers = sources.zip powers := by
    simpa using (List.zip_append (l₁ := sources) (r₁ := extra) (l₂ := powers) (r₂ := []) length)
  simp only [compress, same]

/-- Arbitrary unmatched powers are not multiplied or otherwise inspected. -/
theorem compress_append_powers (width : ℕ) (query : Query) (sources : List (List GoldWord)) (powers extra : List Word)
    (length : sources.length = powers.length) :
    compress width query sources (powers ++ extra) = compress width query sources powers := by
  have same : sources.zip (powers ++ extra) = sources.zip powers := by
    simpa using (List.zip_append (l₁ := sources) (r₁ := []) (l₂ := powers) (r₂ := extra) length)
  simp only [compress, same]

end FormalProof4FHE.HasteBoots.NativeGoldTerminalQuery
