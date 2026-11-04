module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupWords

@[expose] public section

/-!
# Computable Goldilocks lookup selection with retained retry state

Canonical coefficient collection and raw pole checks are executable. Every
rejected offset keeps its receipt and starts a new request; candidate
rejection keeps its existing reader. Fuel bounds analysis prefixes only.
Projection identifies the entire abstract machine and ordered observations.
-/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupSampler

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

def coefficients (values : List ℕ) : Word := fun index =>
  ⟨values[index.val]?.getD 0 % goldilocksModulus,
    (Nat.mod_lt _ (by decide : 0 < goldilocksModulus)).trans (by decide : goldilocksModulus < 2^64)⟩

theorem coefficients_canonical (values : List ℕ) (index : Fin 3) : (coefficients values index).val < goldilocksModulus :=
  Nat.mod_lt _ (by decide)

theorem coefficients_exact (values : List ℕ) (length : values.length = 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) (index : Fin 3) :
    (coefficients values index).val = values[index.val]'(by omega) := by
  simp only [coefficients,List.getElem?_eq_getElem (by omega : index.val < values.length),Option.getD_some]
  exact Nat.mod_eq_of_lt (valid _ (List.getElem_mem (by omega)))

theorem coefficients_decode (values : List ℕ) (length : values.length = 3)
    (valid : ∀ value ∈ values, value < goldilocksModulus) :
    NativeGoldLookupProducer.decode values = some (coefficients values) := by
  rw [NativeGoldLookupProducer.decode_complete values length valid]
  congr 1
  funext index
  apply Fin.ext
  exact (coefficients_exact values length valid index).symm

noncomputable section

theorem coefficients_value (values : List ℕ) : goldExtensionValue (coefficients values) =
    TypedFieldRequest.scalarValue goldilocksBasis values := by
  apply goldilocksBasis.equivFun.injective
  funext index
  simp only [goldExtensionValue,TypedFieldRequest.scalarValue,LinearEquiv.apply_symm_apply,
    coefficients,goldValue,ZMod.natCast_mod]

end

structure Draw where
  value : Word
  coefficients : NativeFieldVector.State

inductive Control where
  | compression (field : NativeFieldVector.State)
  | reciprocal (y : Word) (weights table : List Word) (field : NativeFieldVector.State)
  | finished (y r : Word) (weights table : List Word) (transcript : Transcript)

structure Machine where
  control : Control
  draws : List Draw
  rejected : ℕ

def initial (w : ℕ) (transcript : Transcript) : Program Machine :=
  bind (TypedFieldRequest.beginScalar goldilocksModulus 3 w transcript NativeLookupChallenge.hashLabel)
    (fun field => .pure ⟨.compression field,[],0⟩)

def initialExecute (w : ℕ) (transcript : Transcript) : Machine × List Observation :=
  let started := TypedFieldRequest.beginExecute goldilocksModulus 3 w transcript NativeLookupChallenge.hashLabel
  (⟨.compression started.1,[],0⟩,started.2)

def tick (w width : ℕ) (rows : List (List GoldWord)) (machine : Machine) : Program Machine :=
  match machine.control with
  | .finished _ _ _ _ _ => .pure machine
  | .compression field => bind (NativeFieldVector.drive goldilocksModulus 1 field) (fun result =>
    match result with
    | .suspended field => .pure {machine with control := .compression field}
    | .finished field transcript =>
      let y := coefficients field.values
      let weights := NativeGoldLookup.powers y width
      let table := rows.map (NativeGoldLookup.compress weights)
      bind (TypedFieldRequest.beginScalar goldilocksModulus 3 w transcript NativeLookupChallenge.reciprocalLabel)
        (fun next => .pure ⟨.reciprocal y weights table next,machine.draws ++ [⟨y,field⟩],machine.rejected⟩))
  | .reciprocal y weights table field => bind (NativeFieldVector.drive goldilocksModulus 1 field) (fun result =>
    match result with
    | .suspended field => .pure {machine with control := .reciprocal y weights table field}
    | .finished field transcript =>
      let r := coefficients field.values
      let draws := machine.draws ++ [⟨r,field⟩]
      if NativeGoldLookup.allowed table r then
        .pure ⟨.finished y r weights table transcript,draws,machine.rejected⟩
      else bind (TypedFieldRequest.beginScalar goldilocksModulus 3 w transcript NativeLookupChallenge.reciprocalLabel)
        (fun next => .pure ⟨.reciprocal y weights table next,draws,machine.rejected+1⟩))

def tickExecute (w width : ℕ) (rows : List (List GoldWord)) (machine : Machine) (world : World) : Machine × List Observation :=
  match machine.control with
  | .finished _ _ _ _ _ => (machine,[])
  | .compression field =>
    let trial := NativeFieldVector.driveExecute goldilocksModulus 1 field world
    match trial.1 with
    | .suspended field => ({machine with control := .compression field},trial.2)
    | .finished field transcript =>
      let y := coefficients field.values
      let weights := NativeGoldLookup.powers y width
      let table := rows.map (NativeGoldLookup.compress weights)
      let next := TypedFieldRequest.beginExecute goldilocksModulus 3 w transcript NativeLookupChallenge.reciprocalLabel
      (⟨.reciprocal y weights table next.1,machine.draws ++ [⟨y,field⟩],machine.rejected⟩,trial.2 ++ next.2)
  | .reciprocal y weights table field =>
    let trial := NativeFieldVector.driveExecute goldilocksModulus 1 field world
    match trial.1 with
    | .suspended field => ({machine with control := .reciprocal y weights table field},trial.2)
    | .finished field transcript =>
      let r := coefficients field.values
      let draws := machine.draws ++ [⟨r,field⟩]
      if NativeGoldLookup.allowed table r then (⟨.finished y r weights table transcript,draws,machine.rejected⟩,trial.2)
      else
        let next := TypedFieldRequest.beginExecute goldilocksModulus 3 w transcript NativeLookupChallenge.reciprocalLabel
        (⟨.reciprocal y weights table next.1,draws,machine.rejected+1⟩,trial.2 ++ next.2)

theorem run_initial (w : ℕ) (transcript : Transcript) (world : World) : (run (initial w transcript) world).run = initialExecute w transcript := rfl

theorem run_tick (w width : ℕ) (rows : List (List GoldWord)) (machine : Machine) (world : World) :
    (run (tick w width rows machine) world).run = tickExecute w width rows machine world := by
  cases control : machine.control with
  | finished => simp only [tick,tickExecute,control,OracleProgram.run,CanonicalTranscriptSampler.run_pure]
  | compression field =>
    simp only [tick,tickExecute,control,OracleProgram.run_bind,ObservationReplay.run_bind,NativeFieldVector.run_drive]
    split <;> simp only [OracleProgram.run_bind,ObservationReplay.run_bind,TypedFieldRequest.run_beginScalar,
      OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
  | reciprocal y weights table field =>
    simp only [tick,tickExecute,control,OracleProgram.run_bind,ObservationReplay.run_bind,NativeFieldVector.run_drive]
    split
    · simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]
    · split <;> simp only [OracleProgram.run_bind,ObservationReplay.run_bind,TypedFieldRequest.run_beginScalar,
        OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

def steps (w width : ℕ) (rows : List (List GoldWord)) : ℕ → Machine → Program Machine
  | 0,machine => .pure machine
  | fuel+1,machine => bind (tick w width rows machine) (steps w width rows fuel)

def execute (w width : ℕ) (rows : List (List GoldWord)) : ℕ → Machine → World → Machine × List Observation
  | 0,machine,_ => (machine,[])
  | fuel+1,machine,world =>
    let trial := tickExecute w width rows machine world
    let later := execute w width rows fuel trial.1 world
    (later.1,trial.2 ++ later.2)

theorem run_steps (w width : ℕ) (rows : List (List GoldWord)) (fuel : ℕ) (machine : Machine) (world : World) :
    (run (steps w width rows fuel machine) world).run = execute w width rows fuel machine world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih => simp only [steps,execute,OracleProgram.run_bind,ObservationReplay.run_bind,run_tick,ih]

theorem execute_add (w width : ℕ) (rows : List (List GoldWord)) (first extra : ℕ) (machine : Machine) (world : World) :
    execute w width rows (first+extra) machine world =
      let earlier := execute w width rows first machine world
      let later := execute w width rows extra earlier.1 world
      (later.1,earlier.2 ++ later.2) := by
  induction first generalizing machine with
  | zero => simp only [Nat.zero_add,execute,List.nil_append]
  | succ first ih => simp only [Nat.succ_add,execute,ih,List.append_assoc]

noncomputable section

def projectDraw (draw : Draw) : NativeLookupChallenge.Draw Goldilocks3 := ⟨goldExtensionValue draw.value,draw.coefficients⟩

def projectControl : Control → NativeLookupChallenge.Control Goldilocks3
  | .compression field => .compression field
  | .reciprocal y weights table field => .reciprocal (goldExtensionValue y) (weights.map goldExtensionValue) (table.map goldExtensionValue) field
  | .finished y r weights table transcript => .finished (goldExtensionValue y) (goldExtensionValue r)
      (weights.map goldExtensionValue) (table.map goldExtensionValue) transcript

def project (machine : Machine) : NativeLookupChallenge.Machine Goldilocks3 :=
  ⟨projectControl machine.control,machine.draws.map projectDraw,machine.rejected⟩

theorem project_initial (w : ℕ) (transcript : Transcript) :
    let started := initialExecute w transcript
    (project started.1,started.2) = NativeLookupChallenge.initialExecute (K := Goldilocks3) goldilocksModulus 3 w transcript := rfl

theorem project_tick (w width : ℕ) (rows : List (List GoldWord)) (machine : Machine) (world : World) :
    let trial := tickExecute w width rows machine world
    (project trial.1,trial.2) = NativeLookupChallenge.tickExecute goldilocksBasis w width (rows.map (List.map goldValue)) (project machine) world := by
  cases control : machine.control with
  | finished y r weights table transcript => simp only [tickExecute,control,project,projectControl,NativeLookupChallenge.tickExecute]
  | compression field =>
    simp only [tickExecute,control,project,projectControl,NativeLookupChallenge.tickExecute]
    cases driven : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended field => rfl
    | finished field transcript =>
      simp only [coefficients_value,NativeGoldLookup.powers_value,List.map_append,List.map_singleton,projectDraw,
        NativeGoldLookup.compress_value,List.map_map,Function.comp_def]
  | reciprocal y weights table field =>
    simp only [tickExecute,control,project,projectControl,NativeLookupChallenge.tickExecute]
    cases driven : (NativeFieldVector.driveExecute goldilocksModulus 1 field world).1 with
    | suspended field => rfl
    | finished field transcript =>
      cases accepted : NativeGoldLookup.allowed table (coefficients field.values) <;>
        simp only [← coefficients_value,← NativeGoldLookup.allowed_value,accepted,Bool.false_eq_true,ite_false,ite_true,
          List.map_append,List.map_singleton,projectDraw]

theorem project_execute (w width : ℕ) (rows : List (List GoldWord)) (fuel : ℕ) (machine : Machine) (world : World) :
    let result := execute w width rows fuel machine world
    (project result.1,result.2) = NativeLookupChallenge.execute goldilocksBasis w width (rows.map (List.map goldValue)) fuel (project machine) world := by
  induction fuel generalizing machine with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute,NativeLookupChallenge.execute]
    have tick := project_tick w width rows machine world
    have state := congrArg Prod.fst tick
    have observations := congrArg Prod.snd tick
    simp only at state observations
    rw [← state,← observations,← ih]

end

end FormalProof4FHE.HasteBoots.NativeGoldLookupSampler
