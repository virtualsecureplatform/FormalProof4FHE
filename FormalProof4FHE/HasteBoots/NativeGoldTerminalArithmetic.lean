module

public import FormalProof4FHE.HasteBoots.NativeTerminalField
public import FormalProof4FHE.HasteBoots.NativeGoldInterpolation

@[expose] public section

/-!
# Raw Goldilocks arithmetic of the native lookup terminal guard

Equality, the unsigned prefix loop, ordered full-extension compression and
the terminal residual retain raw operation order. Source elements here are
the outputs of the native query/projection stage; that stage and PCS
acceptance are separate obligations, not replaced by this arithmetic model.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldTerminalArithmetic

open NativeFields NativeFieldWire NativeExtensionFields NativeGoldExtensionArithmetic
open NativeUsizeMessage (Usize)

def equality (first second : List Word) : Word :=
  NativeTerminalCore.equality NativeGoldInterpolation.arithmetic first second

def prefixValue (point : List Word) (count : Usize) : Option Word :=
  NativeTerminalCore.prefixValue NativeGoldInterpolation.arithmetic point count

def compressFrom : List (Word × Word) → Word → Word
  | [], out => out
  | (source, weight) :: rest, out => compressFrom rest (add out (NativeGoldCubic.mul weight source))

def compress (sources powers : List Word) : Word := compressFrom (sources.zip powers) NativeGoldLookup.zero

def residual (r mask source helper : Word) : Word :=
  sub (add (NativeGoldCubic.mul r helper)
    (NativeGoldCubic.mul (NativeGoldCubic.mul mask source) helper)) mask

/-- Arithmetic after native source-query application and padding projection.
It does not stand in for those checked operations. -/
def valueFromElements (eqPoint point : List Word) (count : Usize)
    (r : Word) (sources powers : List Word) (helper : Word) : Option Word :=
  (prefixValue point count).map (fun mask =>
    NativeGoldCubic.mul (equality eqPoint point) (residual r mask (compress sources powers) helper))

def checkFromElements (eqPoint point : List Word) (count : Usize)
    (r : Word) (sources powers : List Word) (helper expected : Word) : Option Bool :=
  (valueFromElements eqPoint point count r sources powers helper).map (fun value => NativeGoldInterpolation.equal value expected)

noncomputable section

private theorem compressFrom_value (pairs : List (Word × Word)) (out : Word) :
    goldExtensionValue (compressFrom pairs out) = goldExtensionValue out +
      (pairs.map (fun pair => goldExtensionValue pair.2 * goldExtensionValue pair.1)).sum := by
  induction pairs generalizing out with
  | nil => simp only [compressFrom, List.map_nil, List.sum_nil, add_zero]
  | cons pair rest ih =>
    simp only [compressFrom, ih, add_value, NativeGoldCubic.mul_value, List.map_cons, List.sum_cons, add_assoc]

theorem compress_value (sources powers : List Word) :
    goldExtensionValue (compress sources powers) =
      ((sources.zip powers).map (fun pair => goldExtensionValue pair.2 * goldExtensionValue pair.1)).sum := by
  rw [compress, compressFrom_value, NativeGoldLookup.zero_value, zero_add]

theorem residual_value (r mask source helper : Word) :
    goldExtensionValue (residual r mask source helper) =
      goldExtensionValue r * goldExtensionValue helper +
        goldExtensionValue mask * goldExtensionValue source * goldExtensionValue helper - goldExtensionValue mask := by
  simp only [residual, sub_value, add_value, NativeGoldCubic.mul_value]

theorem equality_value {n : ℕ} (first second : Fin n → Word) :
    goldExtensionValue (equality (List.ofFn first) (List.ofFn second)) =
      ExtensionLookupIdentity.equality (fun i => goldExtensionValue (first i)) (fun i => goldExtensionValue (second i)) := by
  rw [equality, NativeTerminalCore.equality_map NativeGoldInterpolation.arithmetic_hom,
    List.map_ofFn, List.map_ofFn]
  exact NativeTerminalField.equality_value _ _

theorem prefixValue_value {n : ℕ} (point : Fin n → Word) (count : Usize)
    (shift : n < 64) (enough : count.val ≤ 2 ^ n) :
    (prefixValue (List.ofFn point) count).map goldExtensionValue =
      some (NativePrefixMask.evaluatePrefix (fun i => goldExtensionValue (point i)) count.val enough) := by
  rw [prefixValue, NativeTerminalCore.prefix_map NativeGoldInterpolation.arithmetic_hom, List.map_ofFn]
  exact NativeTerminalField.prefixValue_value _ count shift enough

/-- The exact raw terminal residual evaluates to the same public field
identity used in the lookup soundness argument. -/
theorem valueFromElements_value {n : ℕ} (eqPoint point : Fin n → Word) (count : Usize)
    (shift : n < 64) (enough : count.val ≤ 2 ^ n)
    (r : Word) (sources powers : List Word) (helper : Word) :
    (valueFromElements (List.ofFn eqPoint) (List.ofFn point) count r sources powers helper).map goldExtensionValue =
      some (ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i))
        (fun i => goldExtensionValue (point i)) (goldExtensionValue r)
        (goldExtensionValue (compress sources powers)) (goldExtensionValue helper) count.val enough) := by
  have mask := prefixValue_value point count shift enough
  cases found : prefixValue (List.ofFn point) count with
  | none => rw [found, Option.map_none] at mask; contradiction
  | some rawMask =>
    rw [found, Option.map_some] at mask
    have meaning := Option.some.inj mask
    simp only [valueFromElements, found, Option.map_some]
    rw [NativeGoldCubic.mul_value, equality_value, residual_value, meaning]
    rfl

/-- Native canonical-coordinate equality checks exactly the field terminal
identity, for the actual raw helper and decoded-source elements. -/
theorem checkFromElements_iff {n : ℕ} (eqPoint point : Fin n → Word) (count : Usize)
    (shift : n < 64) (enough : count.val ≤ 2 ^ n)
    (r : Word) (sources powers : List Word) (helper expected : Word) :
    checkFromElements (List.ofFn eqPoint) (List.ofFn point) count r sources powers helper expected = some true ↔
      ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i))
        (fun i => goldExtensionValue (point i)) (goldExtensionValue r)
        (goldExtensionValue (compress sources powers)) (goldExtensionValue helper) count.val enough = goldExtensionValue expected := by
  have semantic := valueFromElements_value eqPoint point count shift enough r sources powers helper
  cases found : valueFromElements (List.ofFn eqPoint) (List.ofFn point) count r sources powers helper with
  | none => rw [found, Option.map_none] at semantic; contradiction
  | some value =>
    rw [found, Option.map_some] at semantic
    have meaning := Option.some.inj semantic
    rw [checkFromElements, found, Option.map_some, Option.some.injEq, NativeGoldInterpolation.equal_value]
    simp only [NativeInterpolationField.arithmetic, decide_eq_true_eq, meaning]

end

end FormalProof4FHE.HasteBoots.NativeGoldTerminalArithmetic
