module

public import FormalProof4FHE.HasteBoots.NativeLookupEquality
public import FormalProof4FHE.HasteBoots.NativeGoldLookupProducer

@[expose] public section

/-!
# Raw equality points from actual completed coefficient readers

Each vector groups consecutive triples of canonical coefficients in native
extension-coordinate order. The actual equality machine supplies lengths,
canonical bounds, point order and the final transcript. No raw point or
coordinate certificate is supplied to the initialized execution theorem.
Analysis suspension is retained; a partial reader is never exported.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldLookupEquality

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeTranscript (Transcript)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)

def wordAt (count : ℕ) (values : List ℕ) (complete : values.length = count * 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) (element : Fin count) : Word := fun coordinate =>
  ⟨values[coordinate.val + 3 * element.val]'(by omega),
    (valid _ (List.getElem_mem (by omega))).trans (by decide)⟩

/-- Checked domain of native consecutive-triple conversion, not a replacement
for the canonical rejection sampler which produced the coefficients. -/
def decodePoint (count : ℕ) (values : List ℕ) : Option (List Word) :=
  if complete : values.length = count * 3 then
    if valid : ∀ value ∈ values, value < goldilocksModulus then
      some (List.ofFn (wordAt count values complete valid)) else none
  else none

theorem decodePoint_complete (count : ℕ) (values : List ℕ) (complete : values.length = count * 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) :
    decodePoint count values = some (List.ofFn (wordAt count values complete valid)) := by
  simp only [decodePoint, dite_eq_left complete, dite_eq_left valid]

structure PointEvidence (count : ℕ) (values : List ℕ) (point : List Word) : Prop where
  length : point.length = count
  coefficients : ∀ (element : ℕ) (inside : element < point.length) (coordinate : Fin 3),
    ((point[element]) coordinate).val = values[coordinate.val + 3 * element]?.getD 0 ∧
      ((point[element]) coordinate).val < goldilocksModulus

noncomputable section

theorem decodePoint_spec (count : ℕ) (values : List ℕ) (point : List Word)
    (success : decodePoint count values = some point) :
    PointEvidence count values point ∧
      point.map goldExtensionValue = List.ofFn (TypedFieldVector.value goldilocksBasis count values) := by
  unfold decodePoint at success
  split at success
  next complete =>
    split at success
    next valid =>
      have same := Option.some.inj success
      subst point
      refine ⟨⟨List.length_ofFn, ?_⟩, ?_⟩
      · intro element inside coordinate
        have elementBound : element < count := by simpa only [List.length_ofFn] using inside
        rw [List.getElem_ofFn]
        have address : coordinate.val + 3 * element < values.length := by omega
        rw [List.getElem?_eq_getElem address]
        exact ⟨rfl, valid _ (List.getElem_mem address)⟩
      · rw [List.map_ofFn]
        apply congrArg List.ofFn
        funext element
        apply goldilocksBasis.equivFun.injective
        ext coordinate
        simp only [Function.comp_def, goldExtension_coordinate, TypedFieldVector.value, LinearEquiv.apply_symm_apply]
        rw [List.getElem?_eq_getElem (by omega : coordinate.val + 3 * element.val < values.length)]
        rfl
    next invalid => contradiction
  next incomplete => contradiction

def decodeDraws {count : ℕ} : List (NativeLookupEquality.Draw count Goldilocks3) → Option (List (List Word))
  | [] => some []
  | draw :: tail => (decodePoint count draw.coefficients.values).bind (fun point =>
      (decodeDraws tail).map (fun points => point :: points))

structure DrawEvidence {count : ℕ} (draw : NativeLookupEquality.Draw count Goldilocks3) (point : List Word) : Prop where
  raw : PointEvidence count draw.coefficients.values point
  value : point.map goldExtensionValue = List.ofFn draw.point

theorem decodeDraws_complete {count : ℕ} (draws : List (NativeLookupEquality.Draw count Goldilocks3))
    (valid : ∀ draw ∈ draws, draw.coefficients.values.length = count * 3 ∧
      NativeFieldVector.ValuesValid goldilocksModulus draw.coefficients) :
    ∃ points, decodeDraws draws = some points := by
  induction draws with
  | nil => exact ⟨[], rfl⟩
  | cons draw tail ih =>
    have good := valid draw List.mem_cons_self
    obtain ⟨points, done⟩ := ih (fun draw member => valid draw (List.mem_cons_of_mem _ member))
    exact ⟨List.ofFn (wordAt count draw.coefficients.values good.1 good.2) :: points,
      by rw [decodeDraws, decodePoint_complete _ _ good.1 good.2, Option.bind_some, done, Option.map_some]⟩

theorem decodeDraws_spec {count : ℕ} (machine : NativeLookupEquality.Machine count Goldilocks3)
    (valid : NativeLookupEquality.Valid goldilocksBasis machine) (draws : List (NativeLookupEquality.Draw count Goldilocks3))
    (contained : ∀ draw ∈ draws, draw ∈ machine.draws) (points : List (List Word))
    (success : decodeDraws draws = some points) : List.Forall₂ DrawEvidence draws points := by
  induction draws generalizing points with
  | nil => have same : [] = points := Option.some.inj success; subst points; exact .nil
  | cons draw tail ih =>
    cases decoded : decodePoint count draw.coefficients.values with
    | none => simp only [decodeDraws, decoded, Option.bind_none] at success; contradiction
    | some point =>
      cases rest : decodeDraws tail with
      | none => simp only [decodeDraws, decoded, Option.bind_some, rest, Option.map_none] at success; contradiction
      | some remaining =>
        have same : point :: remaining = points := Option.some.inj
          (by simpa only [decodeDraws, decoded, Option.bind_some, rest, Option.map_some] using success)
        rw [← same]
        have spec := decodePoint_spec count draw.coefficients.values point decoded
        have actual := (valid.2 draw (contained draw List.mem_cons_self)).2.2
        refine .cons ⟨spec.1, ?_⟩ (ih (fun draw member => contained draw (List.mem_cons_of_mem _ member)) remaining rest)
        rw [spec.2, actual]

structure Output where
  points : List (List Word)
  transcript : Transcript

def finish {count : ℕ} (machine : NativeLookupEquality.Machine count Goldilocks3) : Option Output :=
  if machine.remaining = 0 then (decodeDraws machine.draws).map (fun points => ⟨points, machine.transcript⟩) else none

theorem finish_spec {count : ℕ} (machine : NativeLookupEquality.Machine count Goldilocks3)
    (valid : NativeLookupEquality.Valid goldilocksBasis machine) (output : Output)
    (success : finish machine = some output) :
    machine.remaining = 0 ∧ output.transcript = machine.transcript ∧
      List.Forall₂ DrawEvidence machine.draws output.points := by
  unfold finish at success
  split at success
  next complete =>
    cases decoded : decodeDraws machine.draws with
    | none => simp only [decoded, Option.map_none] at success; contradiction
    | some points =>
      have same : Output.mk points machine.transcript = output := Option.some.inj
        (by simpa only [decoded, Option.map_some] using success)
      rw [← same]
      exact ⟨complete, rfl, decodeDraws_spec machine valid machine.draws (fun _ member => member) points decoded⟩
  next pending => contradiction

/-- This accepts only a completed initialized equality phase and exports
its actual raw points and final child state, preserving all original draws. -/
theorem request_finished (w count fuel : ℕ) (transcript : Transcript) (roots : List Digest)
    (fits : roots.length < 2^64) (world : World)
    (complete : (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w count fuel transcript roots fits) world).run.1.remaining = 0) :
    ∃ output, finish (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w count fuel transcript roots fits) world).run.1 = some output ∧
      output.points.length = roots.length ∧
      List.Forall₂ DrawEvidence
        (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w count fuel transcript roots fits) world).run.1.draws output.points ∧
      output.transcript = (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w count fuel transcript roots fits) world).run.1.transcript ∧
      (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w count fuel transcript roots fits) world).run.1.active = none := by
  let machine := (OracleProgram.run (NativeLookupEquality.request goldilocksBasis w count fuel transcript roots fits) world).run.1
  have valid := NativeLookupEquality.request_valid goldilocksBasis w count fuel transcript roots fits world
  have done := NativeLookupEquality.request_complete goldilocksBasis w count fuel transcript roots fits world complete
  obtain ⟨points, decoded⟩ := decodeDraws_complete machine.draws (fun draw member =>
    ⟨(valid.2 draw member).1, (valid.2 draw member).2.1⟩)
  have evidence := decodeDraws_spec machine valid machine.draws (fun _ member => member) points decoded
  refine ⟨⟨points,machine.transcript⟩, ?_, ?_, evidence, rfl, done.2⟩
  · change finish machine = some ⟨points,machine.transcript⟩
    unfold finish
    rw [ite_eq_left complete, decoded]
    rfl
  · exact evidence.length_eq.symm.trans done.1

end

end FormalProof4FHE.HasteBoots.NativeGoldLookupEquality
