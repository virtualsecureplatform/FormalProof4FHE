module
public import FormalProof4FHE.HasteBoots.AccumulatorShiftQueries
public import FormalProof4FHE.HasteBoots.NativeBlindRotation
public import Mathlib.Data.List.OfFn
@[expose] public section

/-! Pointwise accumulator constraints imply the complete reference blind
rotation. Active rounds retain their original order; padding is not executed.
These are deterministic constraints, not an accepted native proof predicate. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorTrace
open NativeBlindRotation (Cipher Control StepTrace ValidStep ValidTrace)
noncomputable section

structure Shape where
  rounds : ℕ
  padded : ℕ
  positive : 0 < rounds
  fits : rounds ≤ padded

def first (shape : Shape) : Fin shape.padded := ⟨0,by have := shape.positive; have := shape.fits; omega⟩
def last (shape : Shape) : Fin shape.padded := ⟨shape.rounds-1,by have := shape.positive; have := shape.fits; omega⟩
def wrap (shape : Shape) : Fin shape.padded := ⟨shape.padded-1,by have := shape.positive; have := shape.fits; omega⟩
def active (shape : Shape) (round : Fin shape.rounds) : Fin shape.padded :=
  ⟨round.val,lt_of_lt_of_le round.isLt shape.fits⟩
def next (shape : Shape) (row : Fin shape.padded) : Fin shape.padded :=
  ⟨(row.val+1)%shape.padded,Nat.mod_lt _ (by have := shape.positive; have := shape.fits; omega)⟩

structure Tables (q n padded : ℕ) where
  input : Fin padded → Cipher q n
  product : Fin padded → Cipher q n
  difference : Fin padded → Cipher q n
  external : Fin padded → Cipher q n
  output : Fin padded → Cipher q n

variable {q n levels : ℕ}

def Arithmetic {padded : ℕ} (tables : Tables q n padded) : Prop :=
  (∀ row, tables.difference row = tables.product row-tables.input row) ∧
  (∀ row, tables.output row = tables.input row+tables.external row)

/-- Literal coefficient identity behind the native shifted-input check. Both
boundary terms remain when the last active row is also the last padded row. -/
structure Linkage (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n) : Prop where
  initial_eq : tables.input (first shape) = initial
  final_eq : tables.output (last shape) = final
  cyclic : ∀ row, tables.input (next shape row)-tables.output row =
    (if row = wrap shape then initial else 0)-(if row = last shape then final else 0)

theorem active_next (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (link : Linkage shape tables initial final) (round : Fin shape.rounds) (later : round.val+1 < shape.rounds) :
    tables.input ⟨round.val+1,lt_of_lt_of_le later shape.fits⟩ = tables.output (active shape round) := by
  have notWrap : active shape round ≠ wrap shape := by
    intro equal
    have values := congrArg Fin.val equal
    change round.val = shape.padded-1 at values
    have := shape.fits
    omega
  have notLast : active shape round ≠ last shape := by
    intro equal
    have values := congrArg Fin.val equal
    change round.val = shape.rounds-1 at values
    omega
  have identity := link.cyclic (active shape round)
  rw [ite_eq_right notWrap, ite_eq_right notLast, sub_zero] at identity
  have successor : next shape (active shape round) = ⟨round.val+1,lt_of_lt_of_le later shape.fits⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le later shape.fits)
  rw [successor] at identity
  exact sub_eq_zero.mp identity

def traceAt (shape : Shape) (tables : Tables q n shape.padded) (round : Fin shape.rounds) : StepTrace q n where
  product := tables.product (active shape round)
  difference := tables.difference (active shape round)
  external := tables.external (active shape round)
  output := tables.output (active shape round)

theorem validStep_tables (shape : Shape) (tables : Tables q n shape.padded) (arithmetic : Arithmetic tables)
    (bits : ℕ) (control : Control q n levels) (exponent : ℕ) (round : Fin shape.rounds)
    (rotation : tables.product (active shape round) = fun half => NativeBlindRotation.rotate exponent (tables.input (active shape round) half))
    (external : tables.external (active shape round) = NativeBlindRotation.externalProduct bits control (tables.difference (active shape round))) :
    ValidStep bits control exponent (tables.input (active shape round)) (traceAt shape tables round) :=
  ⟨rotation,arithmetic.1 _,external,arithmetic.2 _⟩

/-- Generic indexed-chain lemma. The states include both public endpoints. -/
theorem validTrace_indexed (bits count : ℕ) (controls : Fin count → Control q n levels × ℕ)
    (states : Fin (count+1) → Cipher q n) (traces : Fin count → StepTrace q n)
    (steps : ∀ round, ValidStep bits (controls round).1 (controls round).2 (states round.castSucc) (traces round))
    (advance : ∀ round, (traces round).output = states round.succ) :
    ValidTrace bits (List.ofFn controls) (states 0) (List.ofFn traces) (states (Fin.last count)) := by
  induction count with
  | zero => simp only [List.ofFn_zero, NativeBlindRotation.ValidTrace]; rfl
  | succ count ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    change ValidStep bits (controls 0).1 (controls 0).2 (states 0) (traces 0) ∧ _
    refine ⟨steps 0,?_⟩
    rw [advance 0]
    exact ih (fun round => controls round.succ) (fun round => states round.succ) (fun round => traces round.succ)
      (fun round => steps round.succ) (fun round => advance round.succ)

/-- Only active inputs become states; the terminal state is the public final
accumulator. Original padded rows remain in Tables and in the cyclic relation. -/
def states (shape : Shape) (tables : Tables q n shape.padded) (final : Cipher q n)
    (index : Fin (shape.rounds+1)) : Cipher q n :=
  if bound : index.val < shape.rounds then tables.input (active shape ⟨index.val,bound⟩) else final

theorem states_active (shape : Shape) (tables : Tables q n shape.padded) (final : Cipher q n)
    (round : Fin shape.rounds) : states shape tables final round.castSucc = tables.input (active shape round) := by
  unfold states
  simp only [Fin.val_castSucc]
  rw [dite_eq_left round.isLt]

theorem states_initial (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (link : Linkage shape tables initial final) : states shape tables final 0 = initial := by
  unfold states
  split
  · exact link.initial_eq
  · rename_i impossible
    exact (impossible shape.positive).elim

theorem states_final (shape : Shape) (tables : Tables q n shape.padded) (final : Cipher q n) :
    states shape tables final (Fin.last shape.rounds) = final := by
  unfold states
  simp only [Fin.val_last]
  rw [dite_eq_right (Nat.lt_irrefl shape.rounds)]

theorem states_advance (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (link : Linkage shape tables initial final) (round : Fin shape.rounds) :
    (traceAt shape tables round).output = states shape tables final round.succ := by
  by_cases later : round.val+1 < shape.rounds
  · unfold states
    simp only [Fin.val_succ]
    rw [dite_eq_left later]
    exact (active_next shape tables initial final link round later).symm
  · unfold states
    simp only [Fin.val_succ]
    rw [dite_eq_right later]
    have index : active shape round = last shape := by
      apply Fin.ext
      have := round.isLt
      change round.val = shape.rounds-1
      omega
    change tables.output (active shape round) = final
    rw [index]
    exact link.final_eq

/-- This interface also accepts per-round validity already derived from the
NTT, monomial and external-product stage bridges. -/
theorem validTrace_of_steps (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (link : Linkage shape tables initial final) (bits : ℕ) (controls : Fin shape.rounds → Control q n levels × ℕ)
    (steps : ∀ round, ValidStep bits (controls round).1 (controls round).2
      (tables.input (active shape round)) (traceAt shape tables round)) :
    ValidTrace bits (List.ofFn controls) initial (List.ofFn (traceAt shape tables)) final := by
  have valid := validTrace_indexed bits shape.rounds controls (states shape tables final) (traceAt shape tables)
    (fun round => by rw [states_active]; exact steps round)
    (states_advance shape tables initial final link)
  rw [states_initial shape tables initial final link, states_final] at valid
  exact valid

theorem validTrace_tables (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (arithmetic : Arithmetic tables) (link : Linkage shape tables initial final)
    (bits : ℕ) (controls : Fin shape.rounds → Control q n levels × ℕ)
    (rotation : ∀ round, tables.product (active shape round) = fun half =>
      NativeBlindRotation.rotate (controls round).2 (tables.input (active shape round) half))
    (external : ∀ round, tables.external (active shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1 (tables.difference (active shape round))) :
    ValidTrace bits (List.ofFn controls) initial (List.ofFn (traceAt shape tables)) final := by
  exact validTrace_of_steps shape tables initial final link bits controls
    (fun round => validStep_tables shape tables arithmetic bits _ _ round (rotation round) (external round))

theorem output_eq_run (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (arithmetic : Arithmetic tables) (link : Linkage shape tables initial final)
    (bits : ℕ) (controls : Fin shape.rounds → Control q n levels × ℕ)
    (rotation : ∀ round, tables.product (active shape round) = fun half =>
      NativeBlindRotation.rotate (controls round).2 (tables.input (active shape round) half))
    (external : ∀ round, tables.external (active shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1 (tables.difference (active shape round))) :
    final = NativeBlindRotation.run bits (List.ofFn controls) initial :=
  NativeBlindRotation.validTrace_output bits _ _ _ _
    (validTrace_tables shape tables initial final arithmetic link bits controls rotation external)

/-- A wrong reference output forces a concrete arithmetic or source-stage
failure; no probability or accepted-verifier premise is hidden here. -/
theorem wrong_output_coverage (shape : Shape) (tables : Tables q n shape.padded) (initial final : Cipher q n)
    (bits : ℕ) (controls : Fin shape.rounds → Control q n levels × ℕ)
    (wrong : final ≠ NativeBlindRotation.run bits (List.ofFn controls) initial) :
    ¬Arithmetic tables ∨ ¬Linkage shape tables initial final ∨
      (∃ round, tables.product (active shape round) ≠ fun half =>
        NativeBlindRotation.rotate (controls round).2 (tables.input (active shape round) half)) ∨
      (∃ round, tables.external (active shape round) ≠
        NativeBlindRotation.externalProduct bits (controls round).1 (tables.difference (active shape round))) := by
  classical
  by_contra absent
  push Not at absent
  exact wrong (output_eq_run shape tables initial final absent.1 absent.2.1 bits controls absent.2.2.1 absent.2.2.2)

end
end FormalProof4FHE.HasteBoots.AccumulatorTrace
