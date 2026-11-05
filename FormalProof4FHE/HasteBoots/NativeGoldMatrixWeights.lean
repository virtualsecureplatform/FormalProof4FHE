module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixProduct
public import FormalProof4FHE.HasteBoots.NativeGoldMatrixFill
public import FormalProof4FHE.HasteBoots.FlatMatrixFold

@[expose] public section

/-! Native matrix_weights expands in zero-block/one-block order. Each new
matrix multiplies on the left. Every product uses the original checked raw
payload program; the initial matrix has literal raw zero/one entries. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights

open NativeFieldRepresentation NativeFields
open NativeGoldMatrix (Matrix validate)
open NativeGoldCoefficientsQuery (Pair)

def identity (width : ℕ) : Matrix :=
  ⟨width,NativeGoldMatrixFill.fill width width width (fun row column => if row = column then 1 else 0)⟩

def products (matrix : Matrix) : List Matrix → Option (List Matrix)
  | [] => some []
  | weight :: tail => (NativeGoldMatrixProduct.mul matrix weight).bind (fun product =>
      (products matrix tail).map (fun rest => product :: rest))

def step (width : ℕ) (pair : Pair) (weights : List Matrix) : Option (List Matrix) :=
  if validate pair.zero width && validate pair.one width then
    (products pair.zero weights).bind (fun zero => (products pair.one weights).map (fun one => zero ++ one))
  else none

def loop (width : ℕ) : List Pair → List Matrix → Option (List Matrix)
  | [],weights => some weights
  | pair :: tail,weights => (step width pair weights).bind (loop width tail)

def start (width : ℕ) : Option Matrix :=
  if width*width < 2^64 then NativeGoldMatrix.checked width (identity width).values else none

def weights (width : ℕ) (query : List Pair) : Option (List Matrix) :=
  (start width).bind (fun initial => loop width query [initial])

def Valid (width : ℕ) (matrices : List Matrix) : Prop := ∀ matrix ∈ matrices, validate matrix width = true

def QueryValid (width : ℕ) (query : List Pair) : Prop :=
  ∀ pair ∈ query, validate pair.zero width = true ∧ validate pair.one width = true

theorem identity_valid (width : ℕ) (positive : width ≠ 0) (fits : width*width < 2^64) : validate (identity width) width = true :=
  (NativeGoldMatrix.validate_iff _ _).mpr ⟨positive,rfl,fits,NativeGoldMatrixFill.fill_length _ _ _ _⟩

theorem products_spec (width : ℕ) (matrix : Matrix) (source : List Matrix) (result : List Matrix)
    (left : validate matrix width = true) (valid : Valid width source) (success : products matrix source = some result) :
    result.length = source.length ∧ Valid width result := by
  induction source generalizing result with
  | nil => have same : [] = result := Option.some.inj success; subst result; exact ⟨rfl,by simp [Valid]⟩
  | cons weight tail ih =>
    have right := valid weight List.mem_cons_self
    rw [products,NativeGoldMatrixProduct.mul_success width matrix weight left right,Option.bind_some] at success
    obtain ⟨rest,restRead,same⟩ := Option.map_eq_some_iff.mp success
    subst result
    have previous := ih rest (fun w member => valid w (List.mem_cons_of_mem weight member)) restRead
    refine ⟨by simp only [List.length_cons,previous.1],?_⟩
    intro current member
    rcases List.mem_cons.mp member with same | member
    · subst current; exact NativeGoldMatrixProduct.result_valid _ _ _ _ _
    · exact previous.2 current member

theorem products_complete (width : ℕ) (matrix : Matrix) (source : List Matrix)
    (left : validate matrix width = true) (valid : Valid width source) : ∃ result, products matrix source = some result := by
  induction source with
  | nil => exact ⟨[],rfl⟩
  | cons weight tail ih =>
    have right := valid weight List.mem_cons_self
    obtain ⟨rest,read⟩ := ih (fun w member => valid w (List.mem_cons_of_mem weight member))
    refine ⟨NativeGoldMatrixProduct.result width matrix weight left right :: rest,?_⟩
    simp only [products,NativeGoldMatrixProduct.mul_success width matrix weight left right,Option.bind_some,read,Option.map_some]

theorem step_spec (width : ℕ) (pair : Pair) (source result : List Matrix)
    (pairValid : validate pair.zero width = true ∧ validate pair.one width = true)
    (valid : Valid width source) (success : step width pair source = some result) :
    result.length = 2*source.length ∧ Valid width result := by
  simp only [step,pairValid.1,pairValid.2,Bool.true_and,ite_true,Option.bind_eq_some_iff,Option.map_eq_some_iff] at success
  obtain ⟨zero,readZero,one,readOne,same⟩ := success
  subst result
  have a := products_spec width pair.zero source zero pairValid.1 valid readZero
  have b := products_spec width pair.one source one pairValid.2 valid readOne
  refine ⟨by rw [List.length_append,a.1,b.1]; omega,?_⟩
  intro matrix member
  rcases List.mem_append.mp member with member | member
  · exact a.2 matrix member
  · exact b.2 matrix member

theorem step_complete (width : ℕ) (pair : Pair) (source : List Matrix)
    (pairValid : validate pair.zero width = true ∧ validate pair.one width = true) (valid : Valid width source) :
    ∃ result, step width pair source = some result := by
  obtain ⟨zero,readZero⟩ := products_complete width pair.zero source pairValid.1 valid
  obtain ⟨one,readOne⟩ := products_complete width pair.one source pairValid.2 valid
  exact ⟨zero++one,by simp only [step,pairValid.1,pairValid.2,Bool.true_and,ite_true,readZero,Option.bind_some,readOne,Option.map_some]⟩

theorem loop_spec (width : ℕ) (query : List Pair) (source result : List Matrix)
    (queryValid : QueryValid width query) (valid : Valid width source) (success : loop width query source = some result) :
    result.length = 2^query.length*source.length ∧ Valid width result := by
  induction query generalizing source with
  | nil => have same : source = result := Option.some.inj success; subst result; exact ⟨by simp,valid⟩
  | cons pair tail ih =>
    obtain ⟨next,advanced,rest⟩ := Option.bind_eq_some_iff.mp success
    have step := step_spec width pair source next (queryValid pair List.mem_cons_self) valid advanced
    have previous := ih next (fun p member => queryValid p (List.mem_cons_of_mem pair member)) step.2 rest
    refine ⟨?_,previous.2⟩
    rw [previous.1,step.1,List.length_cons,pow_succ]
    ac_rfl

theorem loop_complete (width : ℕ) (query : List Pair) (source : List Matrix)
    (queryValid : QueryValid width query) (valid : Valid width source) : ∃ result, loop width query source = some result := by
  induction query generalizing source with
  | nil => exact ⟨source,rfl⟩
  | cons pair tail ih =>
    obtain ⟨next,advanced⟩ := step_complete width pair source (queryValid pair List.mem_cons_self) valid
    have good := (step_spec width pair source next (queryValid pair List.mem_cons_self) valid advanced).2
    obtain ⟨result,rest⟩ := ih next (fun p member => queryValid p (List.mem_cons_of_mem pair member)) good
    exact ⟨result,by simp only [loop,advanced,Option.bind_some,rest]⟩

theorem weights_complete (width : ℕ) (query : List Pair) (positive : width ≠ 0) (fits : width*width < 2^64)
    (valid : QueryValid width query) : ∃ result, weights width query = some result ∧ result.length = 2^query.length ∧ Valid width result := by
  have initial := identity_valid width positive fits
  have checked : start width = some (identity width) := by
    rw [start,ite_eq_left fits]
    exact (NativeGoldMatrix.checked_iff _ _ _).mpr ⟨positive,fits,NativeGoldMatrixFill.fill_length _ _ _ _,rfl⟩
  have startValid : Valid width [identity width] := by
    intro matrix member
    have same := List.mem_singleton.mp member
    subst matrix
    exact initial
  obtain ⟨result,read⟩ := loop_complete width query [identity width] valid startValid
  have spec := loop_spec width query [identity width] result valid startValid read
  refine ⟨result,by simp only [weights,checked,Option.bind_some,read],?_,spec.2⟩
  simpa only [List.length_singleton,mul_one] using spec.1

noncomputable section

/-- Total projection; validation below proves every actual getter is bounded. -/
def value (width : ℕ) (matrix : Matrix) : _root_.Matrix (Fin width) (Fin width) Goldilocks :=
  fun row column => goldValue (matrix.values[row.val*width+column.val]?.getD 0)

theorem value_checked (width : ℕ) (matrix : Matrix) (valid : validate matrix width = true) :
    value width matrix = NativeGoldMatrixMeaning.semantic width matrix valid := by
  funext row column
  have bound : row.val*width+column.val < matrix.values.length := by
    rw [(NativeGoldMatrix.validate_iff matrix width).mp valid |>.2.2.2]
    exact NativeGoldMatrixMeaning.address_bound _ _ _
  simp only [value,NativeGoldMatrixMeaning.semantic,List.getElem?_eq_getElem bound,Option.getD_some]

theorem result_value (width : ℕ) (left right : Matrix)
    (leftValid : validate left width = true) (rightValid : validate right width = true) :
    value width (NativeGoldMatrixProduct.result width left right leftValid rightValid) = value width left * value width right := by
  rw [value_checked _ _ (NativeGoldMatrixProduct.result_valid _ _ _ _ _),value_checked _ _ leftValid,value_checked _ _ rightValid]
  exact NativeGoldMatrixProduct.semantic_eq _ _ _ _ _

theorem identity_value (width : ℕ) : value width (identity width) = 1 := by
  funext row column
  have bound := NativeGoldMatrixMeaning.address_bound width row column
  have fits : row.val*width+column.val < (identity width).values.length := by
    rw [identity,NativeGoldMatrixFill.fill_length]
    exact bound
  dsimp only [identity] at fits ⊢
  rw [value,List.getElem?_eq_getElem fits,Option.getD_some]
  change goldValue ((NativeGoldMatrixFill.fill width width width (fun r c => if r = c then 1 else 0))[_]'_) = _
  rw [NativeGoldMatrixFill.fill_get width width width (fun r c => if r = c then 1 else 0) le_rfl le_rfl row column]
  simp only [row.isLt,column.isLt,and_self,ite_true,Fin.val_inj,Matrix.one_apply]
  split <;> simp_all only [goldValue,Nat.cast_one,Fin.val_one,Nat.cast_zero,Fin.val_zero]

/-- Canonical semantic branch expansion in the exact native list order. -/
def semanticStep (width : ℕ) (pair : Pair) (source : List (_root_.Matrix (Fin width) (Fin width) Goldilocks)) :=
  source.map (fun matrix => value width pair.zero * matrix) ++ source.map (fun matrix => value width pair.one * matrix)

def semanticLoop (width : ℕ) : List Pair → List (_root_.Matrix (Fin width) (Fin width) Goldilocks) → List (_root_.Matrix (Fin width) (Fin width) Goldilocks)
  | [],source => source
  | pair :: tail,source => semanticLoop width tail (semanticStep width pair source)

theorem products_value (width : ℕ) (matrix : Matrix) (source result : List Matrix)
    (left : validate matrix width = true) (valid : Valid width source) (success : products matrix source = some result) :
    result.map (value width) = (source.map (value width)).map (fun weight => value width matrix * weight) := by
  induction source generalizing result with
  | nil => have same : [] = result := Option.some.inj success; subst result; rfl
  | cons weight tail ih =>
    have right := valid weight List.mem_cons_self
    rw [products,NativeGoldMatrixProduct.mul_success width matrix weight left right,Option.bind_some] at success
    obtain ⟨rest,read,same⟩ := Option.map_eq_some_iff.mp success
    subst result
    simp only [List.map_cons,result_value,ih rest (fun w member => valid w (List.mem_cons_of_mem weight member)) read]

theorem step_value (width : ℕ) (pair : Pair) (source result : List Matrix)
    (pairValid : validate pair.zero width = true ∧ validate pair.one width = true) (valid : Valid width source)
    (success : step width pair source = some result) : result.map (value width) = semanticStep width pair (source.map (value width)) := by
  simp only [step,pairValid.1,pairValid.2,Bool.true_and,ite_true,Option.bind_eq_some_iff,Option.map_eq_some_iff] at success
  obtain ⟨zero,readZero,one,readOne,same⟩ := success
  subst result
  rw [List.map_append,products_value _ _ _ _ pairValid.1 valid readZero,products_value _ _ _ _ pairValid.2 valid readOne]
  rfl

theorem loop_value (width : ℕ) (query : List Pair) (source result : List Matrix)
    (queryValid : QueryValid width query) (valid : Valid width source) (success : loop width query source = some result) :
    result.map (value width) = semanticLoop width query (source.map (value width)) := by
  induction query generalizing source with
  | nil => have same : source = result := Option.some.inj success; subst result; rfl
  | cons pair tail ih =>
    obtain ⟨next,advanced,rest⟩ := Option.bind_eq_some_iff.mp success
    have nextValid := (step_spec width pair source next (queryValid pair List.mem_cons_self) valid advanced).2
    rw [ih next (fun p member => queryValid p (List.mem_cons_of_mem pair member)) nextValid rest]
    rw [step_value _ _ _ _ (queryValid pair List.mem_cons_self) valid advanced]
    rfl

/-- Successful native expansion has the ordered field semantics, starting at identity. -/
theorem weights_value (width : ℕ) (query : List Pair) (result : List Matrix)
    (positive : width ≠ 0) (fits : width*width < 2^64) (valid : QueryValid width query)
    (success : weights width query = some result) :
    result.map (value width) = semanticLoop width query [1] := by
  have initial := identity_valid width positive fits
  have checked : start width = some (identity width) := by
    rw [start,ite_eq_left fits]
    exact (NativeGoldMatrix.checked_iff _ _ _).mpr
      ⟨positive,fits,NativeGoldMatrixFill.fill_length _ _ _ _,rfl⟩
  rw [weights,checked,Option.bind_some] at success
  have initialValid : Valid width [identity width] := by
    intro matrix member
    have same := List.mem_singleton.mp member
    subst matrix
    exact initial
  simpa only [List.map_singleton,identity_value] using
    loop_value width query [identity width] result valid initialValid success

end

end FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights
