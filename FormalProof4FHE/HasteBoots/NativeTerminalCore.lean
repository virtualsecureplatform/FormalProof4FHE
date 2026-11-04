module

public import FormalProof4FHE.HasteBoots.NativeInterpolationCore
public import FormalProof4FHE.HasteBoots.NativeTerminalBits

@[expose] public section

/-!
# Literal lookup terminal arithmetic loops

Equality retains the native ordered zip/fold. Prefix iteration visits the
actual descending indices and checks every access. The full-table shortcut
precedes the loop. The word-shift domain is explicit; this is not a change
to the native verifier or a claim about unchecked out-of-domain behavior.
-/

namespace FormalProof4FHE.HasteBoots.NativeTerminalCore

open NativeInterpolationCore
open NativeUsizeMessage (Usize)

structure PrefixState (A : Type) where
  same : A
  out : A

def equalityFrom {A : Type} (ops : Arithmetic A) : List (A × A) → A → A
  | [], out => out
  | (x, y) :: rest, out =>
      equalityFrom ops rest (ops.mul out
        (ops.add (ops.mul x y) (ops.mul (ops.sub ops.one x) (ops.sub ops.one y))))

def equality {A : Type} (ops : Arithmetic A) (first second : List A) : A :=
  equalityFrom ops (first.zip second) ops.one

def prefixStep {A : Type} (ops : Arithmetic A) (point : A) (selected : Bool) (state : PrefixState A) : PrefixState A :=
  if selected then
    ⟨ops.mul state.same point, ops.add state.out (ops.mul state.same (ops.sub ops.one point))⟩
  else ⟨ops.mul state.same (ops.sub ops.one point), state.out⟩

def prefixLoop {A : Type} (ops : Arithmetic A) (point : List A) (count : Usize) : ℕ → PrefixState A → Option (PrefixState A)
  | 0, state => some state
  | index + 1, state => (point[index]?).bind (fun value =>
      prefixLoop ops point count index (prefixStep ops value (NativeTerminalBits.bit count index) state))

def prefixValue {A : Type} (ops : Arithmetic A) (point : List A) (count : Usize) : Option A :=
  if point.length < 64 then
    if count.val = 2 ^ point.length then some ops.one
    else (prefixLoop ops point count point.length ⟨ops.one, ops.zero⟩).map PrefixState.out
  else none

def mapPrefix {A B : Type} (f : A → B) (state : PrefixState A) : PrefixState B := ⟨f state.same, f state.out⟩

variable {A B : Type} {source : Arithmetic A} {target : Arithmetic B} {f : A → B}

theorem equalityFrom_map (hom : Hom source target f) (pairs : List (A × A)) (out : A) :
    f (equalityFrom source pairs out) =
      equalityFrom target (pairs.map (fun pair => (f pair.1, f pair.2))) (f out) := by
  induction pairs generalizing out with
  | nil => rfl
  | cons pair rest ih =>
    simp only [equalityFrom, List.map_cons, ih, hom.map_mul, hom.map_add, hom.map_sub, hom.map_one]

theorem equality_map (hom : Hom source target f) (first second : List A) :
    f (equality source first second) = equality target (first.map f) (second.map f) := by
  rw [equality, equalityFrom_map hom]
  simp only [equality, List.zip_map, hom.map_one]
  rfl

theorem prefixStep_map (hom : Hom source target f) (point : A) (selected : Bool) (state : PrefixState A) :
    mapPrefix f (prefixStep source point selected state) =
      prefixStep target (f point) selected (mapPrefix f state) := by
  cases selected <;> simp only [prefixStep, mapPrefix, Bool.false_eq_true, ite_false, ite_true,
    hom.map_mul, hom.map_sub, hom.map_add, hom.map_one]

theorem prefixLoop_map (hom : Hom source target f) (point : List A) (count : Usize)
    (remaining : ℕ) (state : PrefixState A) :
    (prefixLoop source point count remaining state).map (mapPrefix f) =
      prefixLoop target (point.map f) count remaining (mapPrefix f state) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ index ih =>
    simp only [prefixLoop, List.getElem?_map]
    cases found : point[index]? with
    | none => simp only [Option.map_none, Option.bind_none]
    | some value =>
      simp only [Option.map_some, Option.bind_some]
      rw [ih, prefixStep_map hom]

theorem prefix_map (hom : Hom source target f) (point : List A) (count : Usize) :
    (prefixValue source point count).map f = prefixValue target (point.map f) count := by
  simp only [prefixValue, List.length_map]
  by_cases shift : point.length < 64
  · rw [ite_eq_left shift, ite_eq_left shift]
    by_cases full : count.val = 2 ^ point.length
    · simp only [full, ite_true, Option.map_some, hom.map_one]
    · rw [ite_eq_right full, ite_eq_right full]
      have mapped := prefixLoop_map hom point count point.length ⟨source.one, source.zero⟩
      have initial : mapPrefix f ⟨source.one, source.zero⟩ = ⟨target.one, target.zero⟩ := by
        simp only [mapPrefix, hom.map_one, hom.map_zero]
      rw [initial] at mapped
      have projected := congrArg (Option.map PrefixState.out) mapped
      simpa only [Option.map_map, Function.comp_def, mapPrefix] using projected
  · simp only [shift, ite_false, Option.map_none]

end FormalProof4FHE.HasteBoots.NativeTerminalCore
