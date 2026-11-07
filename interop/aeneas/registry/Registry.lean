/-! Checked decoding retains every original registry slot, without a used-slot
filter or alias deduplication. The computed model owner is read back through
the extracted native slice accessor. Heap identity and native initializer body
refinement remain separate. -/
namespace HasteBootsExtractedRegistry
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedRegistryDecode (Source Model decode root)
open formalproof4fhe_native_registry_fixture (registry_get)

def collect : List Source → Option (List Model)
  | [] => some []
  | source::tail => (decode source).bind (fun model => (collect tail).map (model::·))

theorem collect_correct (sources : List Source) (models : List Model)
    (executed : collect sources = some models) :
    List.Forall₂ (fun source model => decode source = some model) sources models := by
  induction sources generalizing models with
  | nil => cases executed; exact .nil
  | cons source tail ih =>
    unfold collect at executed
    cases first : decode source with
    | none => simp only [first,Option.bind_none] at executed; cases executed
    | some model =>
      simp only [first,Option.bind_some] at executed
      cases rest : collect tail with
      | none => simp only [rest,Option.map_none] at executed; cases executed
      | some output =>
        simp only [rest,Option.map_some] at executed
        cases Option.some.inj executed
        exact .cons first (ih output rest)

theorem collect_length (sources : List Source) (models : List Model)
    (executed : collect sources = some models) : models.length = sources.length :=
  (collect_correct sources models executed).length_eq.symm

theorem collect_append (first last : List Source) :
    collect (first++last) = (do let left ← collect first; let right ← collect last; pure (left++right)) := by
  induction first with
  | nil =>
    simp only [List.nil_append,collect]
    cases collect last <;> rfl
  | cons source tail ih =>
    simp only [List.cons_append,collect]
    cases decode source with
    | none => rfl
    | some model =>
      simp only [Option.bind_some]
      rw [ih]
      cases collect tail <;> cases collect last <;> rfl

def registry (source : Slice Source) : Option (NativePrefixCodec.Vector Model) :=
  match executed : collect source.val with
  | none => none
  | some models => some ⟨models,by
      rw [collect_length source.val models executed]
      have bound := HasteBootsExtractedParametersDecode.usize_fits64 (Slice.len source)
      simpa only [Slice.len_val] using bound⟩

theorem registry_values (source : Slice Source) (models : NativePrefixCodec.Vector Model)
    (executed : registry source = some models) : collect source.val = some models.val := by
  unfold registry at executed
  split at executed
  · cases executed
  · rename_i values collected
    have same := Option.some.inj executed
    have valuesEq : values = models.val := congrArg (fun value : NativePrefixCodec.Vector Model => value.val) same
    exact collected.trans (congrArg some valuesEq)

theorem registry_length (source : Slice Source) (models : NativePrefixCodec.Vector Model)
    (executed : registry source = some models) : models.val.length = source.val.length :=
  collect_length source.val models.val (registry_values source models executed)

theorem registry_slot (source : Slice Source) (models : NativePrefixCodec.Vector Model)
    (executed : registry source = some models) (index : Fin models.val.length) :
    ∃ (word : Usize) (entry : Source), word.val = index.val ∧
      registry_get source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
      decode entry = some (models.val.get index) := by
  have lengths := registry_length source models executed
  let sourceIndex : Fin source.val.length := ⟨index.val,by rw [← lengths]; exact index.isLt⟩
  let entry := source.val.get sourceIndex
  have related : decode entry = some (models.val.get index) :=
    (collect_correct source.val models.val (registry_values source models executed)).get sourceIndex.isLt index.isLt
  have before : index.val < (Slice.len source).val := by
    rw [Slice.len_val]
    change index.val < source.val.length
    rw [← lengths]
    exact index.isLt
  let word := Usize.ofNatCore index.val (before.trans (Slice.len source).hBounds)
  have wordValue : word.val = index.val := UScalar.ofNatCore_val_eq _
  have present : source.val[word.val]? = some entry := by
    rw [wordValue]
    exact List.getElem?_eq_getElem sourceIndex.isLt
  exact ⟨word,entry,wordValue,HasteBootsExtractedRegistryProof.get_present source word entry present,related⟩

theorem original_owner_read (source : Slice Source) (models : NativePrefixCodec.Vector Model)
    (decoded : registry source = some models) (parent : NativeTranscript.Transcript)
    (world : InputIndexedOracle.World) (initialized : NativeSourceRegistry.Initialized)
    (executed : (OracleProgram.run (NativeSourceRegistry.startRegistry NativeGoldBlockCode.description.row models parent) world).run.1 = some initialized)
    (position : Fin initialized.sources.val.length) :
    ∃ (original : Fin models.val.length) (word : Usize) (entry : Source),
      original.val = (NativeSourceRegistry.owner initialized.sources position).val ∧ original.val ≤ position.val ∧
      word.val = original.val ∧ registry_get source word = .ok (some (entry.parameters,entry.commitment.root)) ∧
      decode entry = some (models.val.get original) ∧
      (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row
        (models.val.get original).parameters) world).run.1 = some (initialized.sources.val.get position).1 ∧
      root entry.commitment.root = (initialized.sources.val.get position).2 ∧
      ∀ earlier : Fin initialized.sources.val.length, earlier.val < word.val →
        initialized.sources.val.get earlier ≠ initialized.sources.val.get position := by
  obtain ⟨original,ownerEq,before,context,rootEq⟩ := NativeSourceRegistry.initialized_owner
    NativeGoldBlockCode.description.row models parent world initialized executed position
  obtain ⟨word,entry,wordValue,read,entryDecoded⟩ := registry_slot source models decoded original
  have rootValue := (HasteBootsExtractedRegistryDecode.decode_fields entry (models.val.get original) entryDecoded).2
  refine ⟨original,word,entry,ownerEq,before,wordValue,read,entryDecoded,context,rootValue.symm.trans rootEq,?_⟩
  intro earlier earlierBound
  apply NativeSourceRegistry.owner_first initialized.sources position earlier
  simpa only [wordValue,ownerEq] using earlierBound

end HasteBootsExtractedRegistry
