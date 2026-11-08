namespace HasteBootsPointerBoundary
open FormalProof4FHE.HasteBoots.NativePointerStorage

def wordAddress (word : Aeneas.Std.U64) : Address := word.bv.toFin

def addressWord (address : Address) : Aeneas.Std.U64 := ⟨BitVec.ofFin address⟩

theorem word_address_roundtrip (word : Aeneas.Std.U64) : addressWord (wordAddress word) = word := by
  cases word
  rfl

theorem address_word_roundtrip (address : Address) : wordAddress (addressWord address) = address := rfl

theorem address_word_value (address : Address) : (addressWord address).val = address.val := rfl

theorem backend_unit_equal (left right : Aeneas.Std.ConstRawPtr Unit) : left = right := by
  cases left with
  | mk first =>
    cases first
    cases right with
    | mk second =>
      cases second
      rfl

theorem no_null_classifier (encode : Address → Aeneas.Std.ConstRawPtr Unit) :
    ¬ ∃ classify : Aeneas.Std.ConstRawPtr Unit → Bool,
      ∀ address, classify (encode address) = decide (address.val = 0) := by
  rintro ⟨classify, correct⟩
  let zero : Address := ⟨0, by decide⟩
  let one : Address := ⟨1, by decide⟩
  have atZero : classify (encode zero) = true := by simpa only [zero, decide_true] using correct zero
  have atOne : classify (encode one) = false :=
    (correct one).trans (show decide (one.val = 0) = false from by decide)
  rw [backend_unit_equal (encode zero) (encode one)] at atZero
  have impossible : (true : Bool) = false := atZero.symm.trans atOne
  cases impossible

theorem no_nonnull_roundtrip :
    ¬ ∃ (encode : { p : Pointer // NonNull p } → Aeneas.Std.ConstRawPtr Unit)
      (decode : Aeneas.Std.ConstRawPtr Unit → { p : Pointer // NonNull p }),
      ∀ pointer, decode (encode pointer) = pointer := by
  rintro ⟨encode, decode, correct⟩
  let old : { p : Pointer // NonNull p } :=
    ⟨⟨⟨64, by decide⟩, some ⟨9, 0⟩⟩, by change (64 : ℕ) ≠ 0; decide⟩
  let fresh : { p : Pointer // NonNull p } :=
    ⟨⟨⟨64, by decide⟩, some ⟨9, 1⟩⟩, by change (64 : ℕ) ≠ 0; decide⟩
  have same : old = fresh :=
    (correct old).symm.trans ((congrArg decode (backend_unit_equal (encode old) (encode fresh))).trans (correct fresh))
  have generation := congrArg (fun p : { p : Pointer // NonNull p } => p.val.provenance.map Origin.generation) same
  change (some 0 : Option ℕ) = some 1 at generation
  cases generation

end HasteBootsPointerBoundary
