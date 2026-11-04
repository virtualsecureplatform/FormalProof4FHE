module

public import FormalProof4FHE.HasteBoots.NativeTranscriptProgram
public import FormalProof4FHE.HasteBoots.NativeScalarQueryShape
public import FormalProof4FHE.HasteBoots.CanonicalTranscriptSampler
public import Mathlib.Data.List.Sort

@[expose] public section

/-! Classical atomic index requests used by schedule 5. The native power-of-two
and checked byte-count gates run before transcript mutation. Every ordered
word is retained; sorting/deduplication only selects transmitted columns. -/
namespace FormalProof4FHE.HasteBoots.NativeIndexRequest

open InputIndexedOracle (Input World)
open NativeTranscript (Transcript utf8)
open NativeUsizeMessage (Usize)
open OracleProgram (Program bind run)

def check (domain count : Usize) : Bool :=
  NativeScalarQueryShape.powerOfTwo domain.val && decide (count.val * 8 < 2^64)

def prepare (transcript : Transcript) (domain : Usize) : Transcript :=
  NativeTranscript.appendBytes transcript (utf8 "index domain") (TranscriptFrame.littleEndian 8 domain.val)

def word (domain : ℕ) (bytes : Input) : ℕ := TranscriptFrame.fromLittleEndian bytes &&& (domain-1)

def ordered (domain count : ℕ) (bytes : Input) : List ℕ :=
  (List.range count).map (fun index => word domain ((bytes.drop (8*index)).take 8))

/-- Structural evaluation of the unique ascending integer sequence. -/
def distinct (draws : List ℕ) : List ℕ := (draws.insertionSort (fun left right => left ≤ right)).dedup

theorem distinct_eq_mergeSort (draws : List ℕ) : distinct draws =
    (draws.mergeSort (fun left right => decide (left ≤ right))).dedup := by
  rw [List.mergeSort_eq_insertionSort]
  rfl

structure Result where
  draws : List ℕ
  indices : List ℕ
  transcript : Transcript

def request (transcript : Transcript) (label : Input) (domain count : Usize) : Program (Option Result) :=
  if check domain count then
    bind (NativeTranscriptProgram.challengeBytes (prepare transcript domain) label (count.val*8)) (fun (bytes,next) =>
      let draws := ordered domain.val count.val bytes
      .pure (some ⟨draws,distinct draws,next⟩))
  else .pure none

theorem check_iff (domain count : Usize) : check domain count = true ↔
    domain.val.isPowerOfTwo ∧ count.val*8 < 2^64 := by
  simp only [check,Bool.and_eq_true,NativeScalarQueryShape.powerOfTwo_iff,decide_eq_true_eq]

theorem checked_bits (domain count : Usize) (valid : check domain count = true) :
    NativeScalarQueryShape.laneBits domain.val < 64 := by
  have power := (Bool.and_eq_true_iff.mp valid).1
  have same := NativeScalarQueryShape.power_eq_laneBits domain.val power
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
  rw [← same]
  exact domain.isLt

theorem prepare_input (transcript : Transcript) (domain : Usize) :
    (prepare transcript domain).input = transcript.input ++
      TranscriptFrame.encode ⟨1,utf8 "index domain",TranscriptFrame.littleEndian 8 domain.val⟩ := rfl

theorem ordered_length (domain count : ℕ) (bytes : Input) : (ordered domain count bytes).length = count := by
  simp only [ordered,List.length_map,List.length_range]

theorem word_lt (domain : ℕ) (power : NativeScalarQueryShape.powerOfTwo domain = true) (bytes : Input) : word domain bytes < domain := by
  have shape := NativeScalarQueryShape.power_eq_laneBits domain power
  rw [word,shape,Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem ordered_bounded (domain count : ℕ) (bytes : Input) (power : NativeScalarQueryShape.powerOfTwo domain = true) :
    ∀ index ∈ ordered domain count bytes, index < domain := by
  intro index member
  obtain ⟨position,_,same⟩ := List.mem_map.mp member
  subst index
  exact word_lt domain power _

theorem mem_distinct (draws : List ℕ) (index : ℕ) : index ∈ distinct draws ↔ index ∈ draws := by
  simp only [distinct_eq_mergeSort,List.mem_dedup,List.mem_mergeSort]

theorem distinct_nodup (draws : List ℕ) : (distinct draws).Nodup := List.nodup_dedup _

theorem distinct_sorted (draws : List ℕ) : (distinct draws).Pairwise (fun left right => left ≤ right) := by
  have sorted := List.pairwise_mergeSort (le := fun left right : ℕ => decide (left ≤ right))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) draws
  simpa only [distinct_eq_mergeSort,decide_eq_true_eq] using List.Pairwise.sublist (List.dedup_sublist _) sorted

theorem misses_distinct (draws : List ℕ) (bad : Set ℕ) :
    (∀ index ∈ distinct draws, index ∉ bad) ↔ (∀ index ∈ draws, index ∉ bad) := by
  simp only [mem_distinct]

/-- Invalid dimensions issue no challenge and leave no oracle observations. -/
theorem invalid_request (transcript : Transcript) (label : Input) (domain count : Usize) (world : World)
    (invalid : check domain count ≠ true) : (run (request transcript label domain count) world).run = (none,[]) := by
  simp only [request,ite_eq_right invalid,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem accepted_check (transcript : Transcript) (label : Input) (domain count : Usize) (world : World) (result : Result)
    (success : (run (request transcript label domain count) world).run.1 = some result) : check domain count = true := by
  by_contra invalid
  rw [invalid_request _ _ _ _ _ invalid] at success
  contradiction

/-- Exactly one byte request, including count zero, with its ordinary receipt. -/
theorem run_request (transcript : Transcript) (label : Input) (domain count : Usize) (world : World)
    (valid : check domain count = true) :
    (run (request transcript label domain count) world).run =
      let bytes := InputIndexedOracle.bytes world (NativeTranscript.requestInput (prepare transcript domain) label (count.val*8)) 0 (count.val*8)
      let next := (NativeTranscript.challengeBytes world (prepare transcript domain) label (count.val*8)).run.1.2
      (some ⟨ordered domain.val count.val bytes,distinct (ordered domain.val count.val bytes),next⟩,
        [.start (NativeTranscript.requestInput (prepare transcript domain) label (count.val*8)),
         .output (NativeTranscript.requestInput (prepare transcript domain) label (count.val*8)) 0 bytes]) := by
  simp only [request,ite_eq_left valid,OracleProgram.run_bind,ObservationReplay.run_bind,
    NativeTranscriptProgram.run_challengeBytes,NativeTranscript.challengeBytes,NativeTranscript.query,
    OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  rfl

theorem accepted_shape (transcript : Transcript) (label : Input) (domain count : Usize) (world : World) (result : Result)
    (success : (run (request transcript label domain count) world).run.1 = some result) :
    result.draws.length = count.val ∧ result.indices = distinct result.draws ∧ result.indices.Nodup ∧ result.indices.Pairwise (fun left right => left ≤ right) ∧
      (∀ index ∈ result.draws, index < domain.val) ∧ ∀ index ∈ result.indices, index ∈ result.draws := by
  by_cases valid : check domain count = true
  · rw [run_request _ _ _ _ _ valid] at success
    have same := Option.some.inj success
    subst result
    have power := Bool.and_eq_true_iff.mp valid |>.1
    exact ⟨ordered_length _ _ _,rfl,distinct_nodup _,distinct_sorted _,ordered_bounded _ _ _ power,fun index member => (mem_distinct _ _).mp member⟩
  · rw [invalid_request _ _ _ _ _ valid] at success
    contradiction

/-- The literal little-endian mask is the existing finite-byte low-bit map.
Freshness of an actual adaptive transcript request remains a separate premise. -/
theorem word_ofFn (bits : ℕ) (raw : CanonicalByteMask.Bytes 8) :
    word (2^bits) (List.ofFn raw) = (CanonicalByteMask.low bits raw).val := by
  rw [word,CanonicalTranscriptSampler.fromLittleEndian_ofFn]
  exact (CanonicalByteMask.low_val bits raw).symm

/-- Exact word positions in the received atomic block; no truncating zip. -/
theorem ordered_get (domain count : ℕ) (bytes : Input) (index : Fin count) :
    (ordered domain count bytes)[index.val]'(by rw [ordered_length]; exact index.isLt) =
      word domain ((bytes.drop (8*index.val)).take 8) := by
  simp only [ordered,List.getElem_map,List.getElem_range]

theorem slice_length (count : ℕ) (bytes : Input) (length : bytes.length = count*8) (index : Fin count) :
    ((bytes.drop (8*index.val)).take 8).length = 8 := by
  rw [List.length_take,List.length_drop,length]
  have bound := index.isLt
  omega

def typedDraws (bits count : ℕ) (raw : Fin (count*8) → InputIndexedOracle.Byte) : Fin count → Fin (2^bits) :=
  fun index => CanonicalByteMask.low bits (fun position : Fin 8 => raw ⟨8*index.val+position.val,by have a := index.isLt; have b := position.isLt; omega⟩)

theorem slice_ofFn (count : ℕ) (raw : Fin (count*8) → InputIndexedOracle.Byte) (index : Fin count) :
    ((List.ofFn raw).drop (8*index.val)).take 8 = List.ofFn (fun position : Fin 8 =>
      raw ⟨8*index.val+position.val,by have a := index.isLt; have b := position.isLt; omega⟩) := by
  apply List.ext_getElem
  · rw [List.length_ofFn,slice_length _ _ (List.length_ofFn)]
  · intro position inside other
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]

/-- The native block decoder produces the existing with-replacement typed
positions in literal word order. This identifies the values, not freshness. -/
theorem ordered_ofFn (bits count : ℕ) (raw : Fin (count*8) → InputIndexedOracle.Byte) :
    ordered (2^bits) count (List.ofFn raw) = (List.ofFn (typedDraws bits count raw)).map Fin.val := by
  apply List.ext_getElem
  · rw [ordered_length,List.length_map,List.length_ofFn]
  · intro index inside other
    have bound : index < count := by simpa only [ordered_length] using inside
    change (ordered (2^bits) count (List.ofFn raw))[index] = _
    rw [ordered_get _ _ _ ⟨index,bound⟩,slice_ofFn,word_ofFn]
    simp only [List.getElem_map,List.getElem_ofFn,typedDraws]

end FormalProof4FHE.HasteBoots.NativeIndexRequest
