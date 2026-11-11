module
import all FormalProof4FHE.HasteBoots.LookupGuardProducer
import all FormalProof4FHETest.HasteBootsLookupScalarGrammarSmoke
import all FormalProof4FHETest.HasteBootsScalarSourceCausalSmoke

namespace FormalProof4FHE.HasteBoots.LookupNativeTerminalSmoke
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeGoldExtensionArithmetic (Word)
open HasteBootsScalarFinishAncestrySmoke (usize)
open HasteBootsSamplerAncestrySmoke (child)
noncomputable section

def coefficients (values : List ℕ) : NativeFieldVector.State := ⟨⟨child,[],[]⟩,0,values,[]⟩
def draw (values : List ℕ) : NativeLookupChallenge.Draw Goldilocks3 :=
  ⟨TypedFieldRequest.scalarValue goldilocksBasis values,coefficients values⟩
def selection : NativeLookupChallenge.Machine Goldilocks3 :=
  ⟨.finished 0 1 [] [] child,[draw [0,0,0],draw [1,0,0]],0⟩
def produced? := NativeGoldLookupProducer.produce 2 [] selection
theorem present : produced?.isSome = true := by decide +kernel
def output := produced?.get present
theorem produced : NativeGoldLookupProducer.produce 2 [] selection = some output := (Option.some_get present).symm

def point (_ : Fin 2) : Word := NativeGoldLookup.zero
def inputs (_ : Fin 2) (_ : Fin 4) : GoldWord := usize 0

theorem shape : NativeScalarQueryShape.check 0 4 (List.ofFn point).length = true := by decide +kernel

/-- Raw output powers come from the actual native producer, including a zero
second weight. There is no supplied ideal compression challenge. -/
example : output.powers.map (fun word => List.ofFn (fun i => (word i).val)) = [[1,0,0],[0,0,0]] := by decide +kernel
example : ∃ weights : Fin 2 → Word, output.powers = List.ofFn weights ∧
    ∀ i, goldExtensionValue (weights i) = goldExtensionValue output.y^i.val :=
  LookupTerminalDecoding.produced_vector 2 [] selection output produced

/-- The actual constructed query and terminal fold accept these raw vectors. -/
theorem passed : NativeGoldTerminalQuery.constructedCheck 0 4 (List.ofFn point) (List.ofFn point) (usize 0) output.r
    (List.ofFn (fun i => List.ofFn (inputs i))) output.powers NativeGoldLookup.zero NativeGoldLookup.zero = some true := by decide +kernel

/-- Both used source decoders, including the zero-weight one, follow from
that native acceptance, without decoder-success assumptions. -/
example : ∃ decoded : Fin 2 → Goldilocks3,
    ∀ i, PaddedExtension.element goldilocksBasis
      ((ExtensionLookupTerminal.sourceQuery (padding := 1) (c := 2) (row := 0) goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ shape)
        (fun j => goldExtensionValue (point j))).finish (fun lane => goldValue (inputs i lane))) = some (decoded i) := by
  obtain ⟨weights,rawWeights,_⟩ := LookupTerminalDecoding.produced_vector 2 [] selection output produced
  have checked := passed
  rw [rawWeights] at checked
  obtain ⟨decoded,allDecoded,_⟩ := LookupTerminalDecoding.checked_decodes (padding := 1) (row := 0)
    point point shape (usize 0) (by decide) (by decide) output.r inputs weights NativeGoldLookup.zero NativeGoldLookup.zero checked
  exact ⟨decoded,allDecoded⟩

/-- A malformed vector cannot be skipped merely because its weight is zero. -/
example : NativeGoldTerminalQuery.constructedCheck 0 4 (List.ofFn point) (List.ofFn point) (usize 0) output.r
    [[usize 0,usize 0,usize 0,usize 0],[usize 0,usize 0,usize 0]] output.powers NativeGoldLookup.zero NativeGoldLookup.zero = none := by decide +kernel

example : NativeGoldTerminalQuery.constructedCheck 0 4 (List.ofFn point) (List.ofFn point) (usize 0) output.r
    (List.ofFn (fun i => List.ofFn (inputs i))) output.powers NativeGoldLookup.zero NativeGoldLookup.one = some false := by decide +kernel

/-- Full-table checking uses the same literal produced vector and r. -/
theorem fullPassed : NativeGoldTerminalQuery.constructedCheck 0 4 (List.ofFn point) (List.ofFn point) (usize 4) output.r
    (List.ofFn (fun i => List.ofFn (inputs i))) output.powers NativeGoldLookup.one NativeGoldLookup.zero = some true := by decide +kernel

/-- Concrete native acceptance and actual production supply the partial
source expression or a wrong original opening, with separate helper width. -/
example (sources : Fin 2 → MatrixFold.Cube 0 → Fin 4 → NativeFields.Goldilocks)
    (helpers : MatrixFold.Cube 2 → Fin 8 → NativeFields.Goldilocks) :
    goldExtensionValue NativeGoldLookup.zero = ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue output.r)) ExtensionLookupIdentity.partialIndices 2
      (ExtensionLookupIdentity.factors (fun i => goldExtensionValue (point i)) (goldExtensionValue output.y)
        (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) (row := 0) rfl (sources column))
        (fun cell => PaddedExtension.decode (padding := 5) goldilocksBasis (helpers cell)) 0) (List.ofFn point) ∨
      (∃ i, (fun lane => goldValue (inputs i lane)) ≠
        (ExtensionLookupTerminal.sourceQuery (padding := 1) (c := 2) (row := 0) goldilocksBasis rfl
          (fun j => goldExtensionValue (point j))).query.fold (sources i)) ∨
      NativeHelperPacking.coefficients goldilocksBasis 8 (goldExtensionValue NativeGoldLookup.zero) ≠
        (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers :=
  LookupNativeTerminal.partial_or_wrong (padding := 1) (helperPadding := 5) (row := 0) (columns := 2)
    point point shape (usize 0) (by decide) (by decide) [] selection output produced inputs NativeGoldLookup.zero NativeGoldLookup.zero passed sources helpers

example (sources : Fin 2 → MatrixFold.Cube 0 → Fin 4 → NativeFields.Goldilocks)
    (helpers : MatrixFold.Cube 2 → Fin 8 → NativeFields.Goldilocks) :
    goldExtensionValue NativeGoldLookup.zero = ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity
      ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices 2
      (LookupPairArithmetic.fullTables (fun i => goldExtensionValue (point i)) (goldExtensionValue output.r) (goldExtensionValue output.y)
        (fun column => LookupSourceFlattening.flatten (d := 3) (padding := 1) (c := 2) (row := 0) rfl (sources column))
        (fun cell => PaddedExtension.decode (padding := 5) goldilocksBasis (helpers cell))) (List.ofFn point) ∨
      (∃ i, (fun lane => goldValue (inputs i lane)) ≠
        (ExtensionLookupTerminal.sourceQuery (padding := 1) (c := 2) (row := 0) goldilocksBasis rfl
          (fun j => goldExtensionValue (point j))).query.fold (sources i)) ∨
      NativeHelperPacking.coefficients goldilocksBasis 8 (goldExtensionValue NativeGoldLookup.one) ≠
        (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers :=
  LookupNativeTerminal.full_or_wrong (padding := 1) (helperPadding := 5) (row := 0) (columns := 2)
    point point shape (usize 4) (by decide) rfl [] selection output produced inputs NativeGoldLookup.one NativeGoldLookup.zero fullPassed sources helpers

/-- Post-map helper decoding retains the literal native helper, even when
there are no point coordinates. -/
example : PaddedExtension.element goldilocksBasis
    ((ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (Fin.elim0 : Fin 0 → Goldilocks3)).finish
      (NativeHelperPacking.coefficients goldilocksBasis 8 (goldExtensionValue NativeGoldLookup.one))) =
        some (goldExtensionValue NativeGoldLookup.one) := LookupTerminalDecoding.helper_decodes _ _

/-- Every original prelude job has its actual returned guard record at the
same ordinal; no record/job association certificate is a premise. -/
example {count dimension : ℕ} (requests : Fin count → NativeSharedLookupStatement.Request)
    (ready : NativeSharedLookupPrelude.Ready dimension) (sourceValues : List (List GoldWord)) (helperValues : List Word)
    (claims : List NativeScalarBatchVerifier.SubClaim) (sourceVars width : ℕ) (result : NativeSharedLookupGuard.Result)
    (accepted : NativeSharedLookupGuard.guard (NativeSharedLookupPrelude.guardInputs requests ready sourceValues helperValues)
      claims sourceVars width = some result) (index : Fin ready.jobs.length) :
    ∃ checked, result.checked[index.val]? = some checked ∧ checked.ordinal = index.val ∧
      checked.job = NativeSharedLookupGuard.Job.fromProduced (ready.jobs.get index).tag.ordinal.val (ready.jobs.get index).output := by
  obtain ⟨checked,atIndex,ordinal,job,_⟩ := LookupGuardProducer.job_checked requests ready sourceValues helperValues claims sourceVars width result accepted index
  exact ⟨checked,atIndex,ordinal,job⟩

example {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → NativeSharedLookupStatement.Request)
    (n : NativeUsizeMessage.Usize) (multiplicities : List (List GoldWord)) (roots : List NativeRootMessage.Digest)
    (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ) (transcript : NativeTranscript.Transcript)
    (world : InputIndexedOracle.World) (ready : NativeSharedLookupPrelude.Ready n.val)
    (accepted : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits
      w lookupFuel equalityFuel transcript) world).run.1 = some ready) (index : Fin ready.jobs.length) :
    ∃ completed : NativeLookupBatch.Completed NativeFields.goldilocksModulus Goldilocks3,
      NativeGoldLookupProducer.produce (ready.jobs.get index).tag.request.columns (ready.jobs.get index).tag.request.table
        completed.selection = some (ready.jobs.get index).output := by
  obtain ⟨completed,_,_,produced⟩ := LookupGuardProducer.protocol_producer fits requests n multiplicities roots rootFits
    w lookupFuel equalityFuel transcript world ready accepted index
  exact ⟨completed,produced⟩

end
end FormalProof4FHE.HasteBoots.LookupNativeTerminalSmoke
