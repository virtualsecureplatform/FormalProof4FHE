module

public import FormalProof4FHE.HasteBoots.NativeGoldNttSchedule
public import FormalProof4FHE.HasteBoots.NativeGoldNttTwiddles
public import FormalProof4FHE.HasteBoots.NTTButterfly

@[expose] public section

/-! Field interpretation of the actual canonical scalar transform. The proof
uses the computed table and stored-word schedule equalities, rather than a
transform-correctness certificate supplied by the caller. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldNttMeaning

open NativeFields NativeFieldRepresentation
open NativeGoldSolinas (Word value)
open NativeGoldNtt (twiddles stage)
open NativeGoldNttTwiddles

noncomputable section

def base (root : Word) (depth half : ℕ) : Goldilocks := value root^(2*NativeGoldNtt.reverse depth half+1)
def omega (root : Word) (depth : ℕ) : Goldilocks := value root^(2^(depth+1))
def view (data : List Word) (index : ℕ) : Goldilocks := value (data[index]?.getD 0)

theorem child_base (root : Word) (depth half : ℕ) (bit : Bool) :
    base root (depth+1) (half*2+(if bit then 1 else 0)) =
      base root depth half*(if bit then omega root depth else 1) := by
  rw [base,reverse_child]
  cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true,zero_mul,zero_add,mul_one,one_mul]
  · rfl
  · unfold base omega
    have exponent : 2*(2^depth+NativeGoldNtt.reverse depth half)+1 =
        (2*NativeGoldNtt.reverse depth half+1)+2^(depth+1) := by rw [pow_succ]; ring
    rw [exponent,pow_add]

theorem child_omega (root : Word) (depth : ℕ) : omega root (depth+1) = omega root depth^2 := by
  unfold omega
  rw [← pow_mul,pow_succ]

/-- The first actual table read is exactly the semantic subtree twiddle. -/
theorem first_twiddle (total log depth half : ℕ) (root : Word)
    (dimension : total = (log+1)+depth) (halfBound : half < 2^depth) :
    value ((twiddles total root)[2^depth+half]?.getD 0) = base root depth half^(2^log) := by
  subst total
  have bound := NativeGoldNtt.twiddle_address (log+1) log depth half (by omega) halfBound
    (⟨0,by positivity⟩ : Fin (2^(log+1)))
  simp only [Nat.sub_self,pow_zero,one_mul,mul_one,Nat.zero_div,add_zero] at bound
  have fits : 2^depth+half < (twiddles ((log+1)+depth) root).length := by
    rw [NativeGoldNtt.twiddles_length]
    exact bound
  rw [List.getElem?_eq_getElem fits,Option.getD_some,twiddles_value ((log+1)+depth) root ⟨2^depth+half,bound⟩,
    subtree_exponent (log+1) depth half (by omega) halfBound,Nat.add_sub_cancel_right,pow_mul]
  rfl

/-- A top stage uses the same two-half field butterfly in both branches. -/
theorem top_entry (log start index : ℕ) (twid data : List Word) (inside : index < 2^log) (bit : Bool) :
    value (NativeGoldNttStages.entry log start twid data ((if bit then 2^log else 0)+index)) =
      view data index+(if bit then -value (twid[start]?.getD 0) else value (twid[start]?.getD 0))*view data (2^log+index) := by
  have positive : 0 < 2^log := by positivity
  have lowQuot : index/(2*2^log) = 0 := Nat.div_eq_of_lt (by omega)
  have highQuot : (2^log+index)/(2*2^log) = 0 := Nat.div_eq_of_lt (by omega)
  have highHalf : (2^log+index)/2^log = 1 := by
    rw [show 2^log+index = 2^log*1+index by omega,Nat.mul_add_div positive,Nat.div_eq_of_lt inside,add_zero]
  have highMod : (2^log+index)%2^log = index := by
    rw [Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_eq_of_lt inside,Nat.mod_eq_of_lt inside]
  cases bit <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,zero_add,NativeGoldNttStages.entry,lowQuot,highQuot,
      Nat.div_eq_of_lt inside,highHalf,highMod,Nat.mod_eq_of_lt inside,Nat.zero_mod,Nat.one_mod,Nat.one_ne_zero,
      zero_mul,zero_add,add_zero,NativeGoldSolinas.add_value,NativeGoldSolinas.sub_value,NativeGoldSolinas.mul_value,view]
  · rw [Nat.add_comm index (2^log)]
    ring
  · rw [Nat.add_comm index (2^log)]
    ring

def halfData (log : ℕ) (bit : Bool) (data : List Word) : List Word :=
  if bit then data.drop (2^log) else data.take (2^log)

theorem halfData_length (log : ℕ) (bit : Bool) (data : List Word) (size : data.length = 2^(log+1)) :
    (halfData log bit data).length = 2^log := by
  cases bit <;> simp only [halfData,Bool.false_eq_true,ite_false,ite_true,List.length_take,List.length_drop,size,pow_succ]
  · omega
  · omega

theorem half_view (log : ℕ) (bit : Bool) (data : List Word) (index : Fin (2^log)) :
    view (halfData log bit data) index.val = view data ((if bit then 2^log else 0)+index.val) := by
  cases bit <;> simp [halfData,view,List.getElem?_take_of_lt index.isLt]

theorem top_reduced (total log depth half : ℕ) (root : Word) (data : List Word)
    (dimension : total = (log+1)+depth) (halfBound : half < 2^depth) (bit : Bool) :
    (fun index : Fin (2^log) => view (halfData log bit
      (stage (log+1) log (2^depth+half) (twiddles total root) data)) index.val) =
      NTTButterfly.reduced (base root depth half) (fun index => view data index.val) bit := by
  funext index
  have bound : (if bit then 2^log else 0)+index.val < 2^(log+1) := by
    have inside := index.isLt
    rw [pow_succ]
    cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  rw [half_view log bit _ index,view,List.getElem?_eq_getElem (by rw [NativeGoldNtt.stage_length]; exact bound),
    Option.getD_some,NativeGoldNttStages.stage_get (log+1) log (2^depth+half) (twiddles total root) data ⟨_,bound⟩,
    top_entry log (2^depth+half) index.val _ data index.isLt bit,first_twiddle total log depth half root dimension halfBound]
  simp only [NTTButterfly.reduced,NTTButterfly.halves_left_val,NTTButterfly.halves_right_val]

theorem view_append_left (log : ℕ) (left right : List Word) (size : left.length = 2^log) (index : Fin (2^log)) :
    view (left++right) index.val = view left index.val := by
  rw [view,List.getElem?_append_left (by rw [size]; exact index.isLt)]
  rfl

theorem view_append_right (log index : ℕ) (left right : List Word) (size : left.length = 2^log) :
    view (left++right) (2^log+index) = view right index := by
  rw [view,List.getElem?_append_right (by rw [size]; omega),size,Nat.add_sub_cancel_left]
  rfl

/-- Each output of the exact raw recursive tree has the field butterfly
semantics, using the original data and computed full-plan twiddle table. -/
theorem tree_value (total : ℕ) (root : Word) (log depth half : ℕ) (data : List Word)
    (dimension : total = log+depth) (halfBound : half < 2^depth) (size : data.length = 2^log) :
    ∀ cell : MatrixFold.Cube log,
      view (NativeGoldNttSchedule.tree log depth half (twiddles total root) data) (NTTButterfly.outputIndex log cell).val =
        NTTButterfly.transform log (base root depth half) (omega root depth) (fun index => view data index.val) cell := by
  induction log generalizing depth half data with
  | zero =>
    intro cell
    change view data (NTTButterfly.outputIndex 0 cell).val = view data 0
    have same : NTTButterfly.outputIndex 0 cell = 0 := by
      apply Fin.ext
      have bound := (NTTButterfly.outputIndex 0 cell).isLt
      simp only [pow_zero] at bound
      omega
    rw [same]
    rfl
  | succ log ih =>
    rintro ⟨bit,tail⟩
    let next := stage (log+1) log (2^depth+half) (twiddles total root) data
    have nextSize : next.length = 2^(log+1) := NativeGoldNtt.stage_length _ _ _ _ _
    have childBound : half*2+(if bit then 1 else 0) < 2^(depth+1) := by
      rw [pow_succ]
      cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
    have rawChild : view (NativeGoldNttSchedule.tree (log+1) depth half (twiddles total root) data)
        (NTTButterfly.outputIndex (log+1) (bit,tail)).val =
        view (NativeGoldNttSchedule.tree log (depth+1) (half*2+(if bit then 1 else 0)) (twiddles total root)
          (halfData log bit next)) (NTTButterfly.outputIndex log tail).val := by
      cases bit <;> simp only [NativeGoldNttSchedule.tree,NTTButterfly.outputIndex_succ_val,
        Bool.false_eq_true,ite_false,ite_true,halfData,zero_add,add_zero]
      · apply view_append_left
        exact NativeGoldNttSchedule.tree_length _ _ _ _ _ (halfData_length log false next nextSize)
      · apply view_append_right
        exact NativeGoldNttSchedule.tree_length _ _ _ _ _ (halfData_length log false next nextSize)
    rw [rawChild,ih (depth+1) _ _ (by omega) childBound (halfData_length log bit next nextSize) tail,
      NTTButterfly.transform,child_base,child_omega,top_reduced total log depth half root data dimension halfBound bit]

/-- The actual cutoff-based scalar transform has the existing flat field
butterfly semantics in its original contiguous output order. -/
theorem depthFirst_value (log : ℕ) (root : Word) (data : List Word) (size : data.length = 2^log) :
    (NativeGoldNtt.depthFirst log 0 0 (twiddles log root) data).map value =
      List.ofFn (NTTButterfly.flatTransform log (value root) (value root^2) (fun index => view data index.val)) := by
  rw [NativeGoldNttSchedule.depthFirst_tree _ _ _ _ _ size]
  apply List.ext_getElem (by rw [List.length_map,NativeGoldNttSchedule.tree_length _ _ _ _ _ size,List.length_ofFn])
  intro index inside other
  have bound : index < 2^log := by simpa only [List.length_ofFn] using other
  simp only [List.getElem_map,List.getElem_ofFn]
  have projected := tree_value log root log 0 0 data (by omega) (by decide) size
    ((NTTButterfly.outputIndex log).symm ⟨index,bound⟩)
  simp only [Equiv.apply_symm_apply,base,NativeGoldNtt.reverse,mul_zero,zero_add,pow_one,omega] at projected
  have present : index < (NativeGoldNttSchedule.tree log 0 0 (twiddles log root) data).length := by
    rw [NativeGoldNttSchedule.tree_length _ _ _ _ _ size]
    exact bound
  simpa only [view,List.getElem?_eq_getElem present,Option.getD_some,NTTButterfly.flatTransform] using projected

/-- Canonicalization and raw output conversion preserve the interpretation
of every original u64 coefficient. No scalar-transform certificate is assumed. -/
theorem forwardData_value (log : ℕ) (root : Word) (data : List GoldWord) (size : data.length = 2^log) :
    (NativeGoldNtt.forwardData log root data).map goldValue =
      List.ofFn (NTTButterfly.flatTransform log (value root) (value root^2)
        (fun index => goldValue (data[index.val]?.getD 0))) := by
  rw [NativeGoldNtt.forwardData,List.map_map]
  change (NativeGoldNtt.depthFirst log 0 0 (twiddles log root) (data.map NativeGoldSolinas.canonical)).map value = _
  rw [depthFirst_value _ _ _ (by rw [List.length_map,size])]
  congr 1
  congr 1
  funext index
  have bound : index.val < data.length := by rw [size]; exact index.isLt
  simp only [view,List.getElem?_map,List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some,NativeGoldSolinas.canonical_value]

/-- The scalar program evaluates the original coefficient polynomial on the
native bit-reversed odd-root domain whenever the trusted root is primitive. -/
theorem forwardData_evaluation (log : ℕ) (root : Word) (data : List GoldWord) (size : data.length = 2^log)
    (primitive : IsPrimitiveRoot (value root) (2^(log+1))) :
    (NativeGoldNtt.forwardData log root data).map goldValue =
      List.ofFn (NTTRowCheck.evaluation (NTTButterfly.nodes log (value root))
        (fun index => goldValue (data[index.val]?.getD 0))) := by
  rw [forwardData_value log root data size,NTTButterfly.negacyclic_evaluation log (value root) primitive]

/-- The checked public forward API inherits the same evaluation semantics. -/
theorem forward_evaluation (log : ℕ) (root : Word) (data result : List GoldWord)
    (success : NativeGoldNtt.forward log root data = some result)
    (primitive : IsPrimitiveRoot (value root) (2^(log+1))) :
    result.map goldValue = List.ofFn (NTTRowCheck.evaluation (NTTButterfly.nodes log (value root))
      (fun index => goldValue (data[index.val]?.getD 0))) := by
  unfold NativeGoldNtt.forward at success
  split at success
  · split at success
    · rename_i size
      have same := Option.some.inj success
      subst result
      exact forwardData_evaluation log root data size primitive
    · contradiction
  · contradiction

end
end FormalProof4FHE.HasteBoots.NativeGoldNttMeaning
