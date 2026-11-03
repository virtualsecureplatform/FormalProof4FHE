module

public import FormalProof4FHE.HasteBoots.NativePublic

@[expose] public section

/-!
# Coefficient-domain binary blind rotation

Explicit reference arithmetic for the recurrence in
`fhe_core/src/blind_rotation/rlwe/binary.rs`. A control consists of the two
families of gadget RLWE rows already present in the public key: nonce rows
(`false`, encrypting -s*m) and body rows (`true`, encrypting m).
The reference uses full unsigned radix digits and negacyclic convolution.
Equality with the NTT implementation and the chosen native gadget parameters
are refinement obligations, not assumptions discharged by this file.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NativeBlindRotation

abbrev Poly (q n : ℕ) := Fin n → ZMod q
abbrev Cipher (q n : ℕ) := Bool → Poly q n
abbrev Control (q n levels : ℕ) := Bool → Fin levels → Cipher q n

variable {q n levels : ℕ}

/-- Literal multiplication modulo X^N+1; an upper convolution coefficient wraps with a minus sign. -/
def mul (left right : Poly q n) (index : Fin n) : ZMod q :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i.val + j.val) % n = index.val then
      if i.val + j.val < n then left i * right j else -(left i * right j)
    else 0

/-- Signed monomial action, defined by the coefficient scatter rather than an NTT. -/
def rotate (exponent : ℕ) (poly : Poly q n) (index : Fin n) : ZMod q :=
  ∑ j : Fin n,
    let target := (j.val + exponent) % (2 * n)
    if target < n then
      if index.val = target then poly j else 0
    else if index.val + n = target then -poly j else 0

theorem rotate_zero (poly : Poly q n) : rotate 0 poly = poly := by
  classical
  funext index
  unfold rotate
  rw [Finset.sum_eq_single index]
  · have bound : index.val < 2 * n := by omega
    simp [Nat.mod_eq_of_lt bound, index.isLt]
  · intro j _ different
    have bound : j.val < 2 * n := by omega
    have unequal : index.val ≠ j.val := fun h => different (Fin.ext h.symm)
    simp [Nat.mod_eq_of_lt bound, j.isLt, unequal]
  · simp

/-- Canonical unsigned digit at one radix position. -/
def digit (bits : ℕ) (level : Fin levels) (poly : Poly q n) : Poly q n :=
  fun i => ((poly i).val / (2 ^ bits) ^ level.val % (2 ^ bits) : ℕ)

/-- Both ciphertext halves and all gadget levels contribute to each output half. -/
def externalProduct (bits : ℕ) (control : Control q n levels) (input : Cipher q n) :
    Cipher q n :=
  fun half index => ∑ source : Bool, ∑ level : Fin levels,
    mul (digit bits level (input source)) (control source level half) index

/-- The traced path performs every round, including exponent-zero rounds. -/
def step (bits : ℕ) (control : Control q n levels) (exponent : ℕ)
    (acc : Cipher q n) : Cipher q n :=
  acc + externalProduct bits control ((fun half => rotate exponent (acc half)) - acc)

theorem externalProduct_zero (bits : ℕ) (control : Control q n levels) :
    externalProduct bits control 0 = 0 := by
  classical
  funext half index
  simp [externalProduct, digit, mul]

/-- The zero-rotation round retained by the traced evaluator is an identity step. -/
theorem step_zero (bits : ℕ) (control : Control q n levels) (acc : Cipher q n) :
    step bits control 0 acc = acc := by
  simp [step, rotate_zero, externalProduct_zero]

structure StepTrace (q n : ℕ) where
  product : Cipher q n
  difference : Cipher q n
  external : Cipher q n
  output : Cipher q n

/-- Independent arithmetic constraints: no proof-system verifier occurs here. -/
def ValidStep (bits : ℕ) (control : Control q n levels) (exponent : ℕ)
    (acc : Cipher q n) (trace : StepTrace q n) : Prop :=
  trace.product = (fun half => rotate exponent (acc half)) ∧
  trace.difference = trace.product - acc ∧
  trace.external = externalProduct bits control trace.difference ∧
  trace.output = acc + trace.external

def makeStep (bits : ℕ) (control : Control q n levels) (exponent : ℕ)
    (acc : Cipher q n) : StepTrace q n :=
  let product := fun half => rotate exponent (acc half)
  let difference := product - acc
  let external := externalProduct bits control difference
  ⟨product, difference, external, acc + external⟩

theorem makeStep_valid (bits : ℕ) (control : Control q n levels) (exponent : ℕ)
    (acc : Cipher q n) : ValidStep bits control exponent acc (makeStep bits control exponent acc) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem validStep_output (bits : ℕ) (control : Control q n levels) (exponent : ℕ)
    (acc : Cipher q n) (trace : StepTrace q n)
    (valid : ValidStep bits control exponent acc trace) :
    trace.output = step bits control exponent acc := by
  rcases valid with ⟨hp, hd, he, ho⟩
  rw [ho, he, hd, hp]
  rfl

abbrev Controls (q n levels : ℕ) := List (Control q n levels × ℕ)

def run (bits : ℕ) : Controls q n levels → Cipher q n → Cipher q n
  | [], acc => acc
  | (control, exponent) :: rest, acc => run bits rest (step bits control exponent acc)

def ValidTrace (bits : ℕ) : Controls q n levels → Cipher q n →
    List (StepTrace q n) → Cipher q n → Prop
  | [], acc, [], output => output = acc
  | (control, exponent) :: rest, acc, t :: ts, output =>
      ValidStep bits control exponent acc t ∧ ValidTrace bits rest t.output ts output
  | _, _, _, _ => False

/-- Every satisfying trace has the unique output of the explicit reference computation. -/
theorem validTrace_output (bits : ℕ) (controls : Controls q n levels)
    (acc : Cipher q n) (trace : List (StepTrace q n)) (output : Cipher q n)
    (valid : ValidTrace bits controls acc trace output) : output = run bits controls acc := by
  induction controls generalizing acc trace with
  | nil => cases trace <;> simp_all [ValidTrace, run]
  | cons control rest ih =>
    rcases control with ⟨key, exponent⟩
    cases trace with
    | nil => simp [ValidTrace] at valid
    | cons t ts =>
      obtain ⟨hs, ht⟩ := valid
      rw [run, ← validStep_output bits key exponent acc t hs]
      exact ih t.output ts ht

/-- Public evaluation constructs a full arithmetic witness, without a secret key. -/
def makeTrace (bits : ℕ) : Controls q n levels → Cipher q n → List (StepTrace q n)
  | [], _ => []
  | (control, exponent) :: rest, acc =>
      let t := makeStep bits control exponent acc
      t :: makeTrace bits rest t.output

theorem makeTrace_valid (bits : ℕ) (controls : Controls q n levels) (acc : Cipher q n) :
    ValidTrace bits controls acc (makeTrace bits controls acc) (run bits controls acc) := by
  induction controls generalizing acc with
  | nil => rfl
  | cons control rest ih =>
    rcases control with ⟨key, exponent⟩
    exact ⟨makeStep_valid bits key exponent acc, ih (step bits key exponent acc)⟩

end FormalProof4FHE.HasteBoots.NativeBlindRotation
