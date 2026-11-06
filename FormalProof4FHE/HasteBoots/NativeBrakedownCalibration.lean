module
public import FormalProof4FHE.HasteBoots.RectangularPCSParameters
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCode
public import FormalProof4FHE.HasteBoots.NativeFields
@[expose] public section

/-! Exact candidate arithmetic for original-size protocol-12/schedule-5
Brakedown roles with helper-basis tests. Quotas remain configurable: the
certificates below require at least 544 ordered draws. This is not an
implementation-refinement or whole-PBS expected-work theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeBrakedownCalibration
open RectangularPCSParameters (finiteProximity finiteColumns finiteError)
open PCSParameters (distance)
noncomputable section

inductive Field where | goldilocks | babyBear
  deriving DecidableEq
inductive Role where | source | helper | finalSource | finalHelper
  deriving DecidableEq

def polynomialSize : ℕ := 1024
def lweDimension : ℕ := 728

def prime : Field → ℕ
  | .goldilocks => NativeFields.goldilocksModulus
  | .babyBear => NativeFields.babyBearModulus

def codeWidth : Field → ℕ | .goldilocks => 4 | .babyBear => 8

def testWidth (field : Field) : Role → ℕ
  | .source | .finalSource => codeWidth field
  | .helper | .finalHelper => match field with | .goldilocks => 3 | .babyBear => 6

def roleVariables (field : Field) (role : Role) : ℕ :=
  let short := NativeGoldBlockCode.nextLog (2*polynomialSize/codeWidth field)
  let rounds := NativeGoldBlockCode.nextLog lweDimension
  let lanes := NativeGoldBlockCode.nextLog (codeWidth field)
  match role with
  | .source => short+rounds
  | .helper => short+rounds+lanes
  | .finalSource => short
  | .finalHelper => short+lanes

def left (field : Field) (role : Role) : ℕ := roleVariables field role / 2

def message (field : Field) (role : Role) : ℕ :=
  NativeGoldBlockCode.paddedBlocks (2^(roleVariables field role-left field role)) (codeWidth field)

def domain (field : Field) (role : Role) : ℕ :=
  NativeGoldBlockCode.domainBlocks (2^(roleVariables field role-left field role)) (codeWidth field) 2

def height (field : Field) (role : Role) : ℕ := (domain field role).size-1

def radius (field : Field) (role : Role) : ℕ := (distance (height field role) (message field role)-1)/3

def proximity (field : Field) (role : Role) : NNReal :=
  finiteProximity (prime field) (testWidth field role) (height field role) (message field role)

def columns (field : Field) (role : Role) (queries : ℕ) : NNReal :=
  finiteColumns (height field role) (message field role) queries (radius field role)

def error (field : Field) (role : Role) (queries : ℕ) : NNReal := proximity field role + columns field role queries

def dimensions : Field → Role → ℕ × ℕ × ℕ
  | .goldilocks,.source => (9,256,4)
  | .goldilocks,.helper => (10,512,3)
  | .goldilocks,.finalSource => (5,8,4)
  | .goldilocks,.finalHelper => (5,16,3)
  | .babyBear,.source => (7,64,8)
  | .babyBear,.helper => (9,256,6)
  | .babyBear,.finalSource => (5,2,8)
  | .babyBear,.finalHelper => (5,8,6)

theorem geometry (field : Field) (role : Role) :
    (height field role,message field role,testWidth field role) = dimensions field role := by
  cases field <;> cases role <;> decide +kernel

theorem height_eq (field : Field) (role : Role) : height field role = (dimensions field role).1 :=
  congrArg Prod.fst (geometry field role)
theorem message_eq (field : Field) (role : Role) : message field role = (dimensions field role).2.1 :=
  congrArg (fun value => value.2.1) (geometry field role)
theorem testWidth_eq (field : Field) (role : Role) : testWidth field role = (dimensions field role).2.2 :=
  congrArg (fun value => value.2.2) (geometry field role)

theorem domains (field : Field) (role : Role) : 2^(height field role) = domain field role := by
  cases field <;> cases role <;> decide +kernel

theorem radius_valid (field : Field) (role : Role) :
    radius field role < prime field ∧ 3*radius field role < distance (height field role) (message field role) := by
  cases field <;> cases role <;> decide +kernel

theorem column_ratios (field : Field) (role : Role) :
    (((2^(height field role)-(distance (height field role) (message field role)-radius field role) : ℕ) : NNReal)/(2^(height field role) : ℕ)) ≤ 5/6 ∧
    (((2^(height field role)-(radius field role+1) : ℕ) : NNReal)/(2^(height field role) : ℕ)) ≤ 5/6 := by
  cases field <;> cases role <;> constructor <;> rw [← NNReal.coe_le_coe] <;>
    norm_num [radius,height_eq,message_eq,dimensions,distance]

theorem proximity_gold (role : Role) : proximity .goldilocks role ≤ 1/2^164 := by
  cases role <;> rw [← NNReal.coe_le_coe] <;>
    norm_num [proximity,finiteProximity,prime,NativeFields.goldilocksModulus,testWidth_eq,height_eq,message_eq,dimensions,distance]

theorem proximity_babyBear (role : Role) : proximity .babyBear role ≤ 1/2^137 := by
  cases role <;> rw [← NNReal.coe_le_coe] <;>
    norm_num [proximity,finiteProximity,prime,NativeFields.babyBearModulus,testWidth_eq,height_eq,message_eq,dimensions,distance]

theorem fiveSixths_544 : (5/6 : NNReal)^544 ≤ 1/2^141 := by
  have block : (5/6 : NNReal)^27 ≤ 1/2^7 := by rw [← NNReal.coe_le_coe]; norm_num
  have tail : (5/6 : NNReal)^4 ≤ 1/2 := by rw [← NNReal.coe_le_coe]; norm_num
  calc
    _ = ((5/6 : NNReal)^27)^20 * (5/6 : NNReal)^4 := by rw [← pow_mul,← pow_add]
    _ ≤ (1/2^7 : NNReal)^20 * (1/2 : NNReal) := mul_le_mul' (pow_le_pow_left' block 20) tail
    _ = _ := by norm_num

theorem columns_le (field : Field) (role : Role) (queries : ℕ) (enough : 544 ≤ queries) :
    columns field role queries ≤ 1/2^141 := by
  obtain ⟨near,far⟩ := column_ratios field role
  have base : (5/6 : NNReal) ≤ 1 := by rw [← NNReal.coe_le_coe]; norm_num
  apply le_trans _ fiveSixths_544
  apply le_trans _ (pow_le_pow_right_of_le_one' base enough)
  exact max_le (pow_le_pow_left' near queries) (pow_le_pow_left' far queries)
theorem prime_nonzero (field : Field) : prime field ≠ 0 := by cases field <;> decide +kernel

theorem error_le (field : Field) (role : Role) (queries : ℕ) (enough : 544 ≤ queries) :
    error field role queries ≤ 17/2^141 := by
  have fieldBound : proximity field role ≤ 1/2^137 := by
    cases field with
    | babyBear => exact proximity_babyBear role
    | goldilocks =>
      apply (proximity_gold role).trans
      rw [← NNReal.coe_le_coe]
      norm_num
  have combined := add_le_add fieldBound (columns_le field role queries enough)
  calc
    _ ≤ (1/2^137 : NNReal)+1/2^141 := combined
    _ = _ := by norm_num

def totalError (field : Field) (queries : ℕ) : NNReal :=
  error field .source queries + error field .helper queries + error field .finalSource queries + error field .finalHelper queries

theorem totalError_le (field : Field) (queries : ℕ) (enough : 544 ≤ queries) :
    totalError field queries ≤ 17/2^139 := by
  have bounded := add_le_add (add_le_add (add_le_add (error_le field .source queries enough) (error_le field .helper queries enough))
    (error_le field .finalSource queries enough)) (error_le field .finalHelper queries enough)
  calc
    _ ≤ (17/2^141 : NNReal)+17/2^141+17/2^141+17/2^141 := bounded
    _ = _ := by norm_num

/-- An arithmetic allowance for all64 native shapes and the four roles.
The finite shape domain is not an attacker trial or lifetime cap. This lemma
does not itself establish how the application consumes that allowance. -/
theorem shape_allowance (field : Field) (queries : ℕ) (enough : 544 ≤ queries) :
    (2 : NNReal)^128 * (64*totalError field queries) ≤ 17/32 := by
  have bounded := mul_le_mul' (le_refl ((2 : NNReal)^128)) (mul_le_mul' (le_refl (64 : NNReal)) (totalError_le field queries enough))
  calc
    _ ≤ (2 : NNReal)^128*(64*(17/2^139)) := bounded
    _ = _ := by norm_num

theorem error_ennreal_le (field : Field) (role : Role) (queries : ℕ) (enough : 544 ≤ queries) :
    RectangularPCSParameters.error (prime field) (testWidth field role) (height field role) (message field role) queries (radius field role) ≤
      (17 : ENNReal)/2^141 := by
  have finite : finiteError (prime field) (testWidth field role) (height field role) (message field role) queries (radius field role) ≤
      (17 : NNReal)/2^141 := error_le field role queries enough
  have cast := ENNReal.coe_le_coe.mpr finite
  rw [RectangularPCSParameters.finiteError_coe _ _ _ _ _ _ (prime_nonzero field)] at cast
  have nonzero : (2 : NNReal)^141 ≠ 0 := by positivity
  simpa only [ENNReal.coe_div nonzero,ENNReal.coe_pow,ENNReal.coe_ofNat] using cast

/-- Distinct trusted quotas for the four native roles are also supported. -/
def roleError (field : Field) (queries : Role → ℕ) : NNReal :=
  error field .source (queries .source) + error field .helper (queries .helper) +
    error field .finalSource (queries .finalSource) + error field .finalHelper (queries .finalHelper)

theorem roleError_le (field : Field) (queries : Role → ℕ) (enough : ∀ role, 544 ≤ queries role) :
    roleError field queries ≤ 17/2^139 := by
  have bounded := add_le_add (add_le_add (add_le_add (error_le field .source _ (enough .source)) (error_le field .helper _ (enough .helper)))
    (error_le field .finalSource _ (enough .finalSource))) (error_le field .finalHelper _ (enough .finalHelper))
  calc
    _ ≤ (17/2^141 : NNReal)+17/2^141+17/2^141+17/2^141 := bounded
    _ = _ := by norm_num

theorem role_shape_allowance (field : Field) (queries : Role → ℕ) (enough : ∀ role, 544 ≤ queries role) :
    (2 : NNReal)^128 * (64*roleError field queries) ≤ 17/32 := by
  have bounded := mul_le_mul' (le_refl ((2 : NNReal)^128)) (mul_le_mul' (le_refl (64 : NNReal)) (roleError_le field queries enough))
  calc
    _ ≤ (2 : NNReal)^128*(64*(17/2^139)) := bounded
    _ = _ := by norm_num

end
end FormalProof4FHE.HasteBoots.NativeBrakedownCalibration
