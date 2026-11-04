module

public import FormalProof4FHE.HasteBoots.NativeLookupBindGeometry
public import FormalProof4FHE.HasteBoots.NativeSharedLookupStatement

@[expose] public section

/-!
# Numeric shared lookup preflight in native request order

All registry entries, including unused ones, share logical dimensions.
Each request gathers its original slots, runs the numeric bind prefix,
checks the common geometry and then adds repetitions with checked usize
arithmetic. Returned bindings are computed trace metadata, not proof input.
Canonical configuration validation, contexts and framing remain separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeSharedLookupPreflight

open NativeUsizeMessage (Usize)
open NativeLookupBindGeometry (Parameters)
open NativeSharedLookupStatement (Request)

abbrev Geometry := Usize × Usize

def key (geometry : NativeLookupBindGeometry.Output) : Geometry := ⟨geometry.numVariables,geometry.width⟩

def gather (registry : List Parameters) : List ℕ → Option (List Parameters)
  | [] => some []
  | slot :: tail => registry[slot]?.bind (fun source => (gather registry tail).map (fun rest => source :: rest))

def registryDimensions (registry : List Parameters) (requests : List Request) : Bool :=
  decide (registry ≠ []) && decide (requests ≠ []) && requests.all (fun request =>
    decide (request.terminal.sourceSlots.length = request.columns) &&
      request.terminal.sourceSlots.all (fun slot => decide (slot < registry.length)))

def uniform (registry : List Parameters) : Bool :=
  match registry.head? with
  | none => false
  | some first => registry.all (fun source => decide (source = first))

def addRepetitions (previous : Usize) (repetitions : ℕ) : Option Usize :=
  if fits : previous.val + repetitions < 2^64 then some ⟨previous.val + repetitions,fits⟩ else none

structure Binding where
  request : Request
  sources : List Parameters
  geometry : NativeLookupBindGeometry.Output

structure State where
  geometry : Option Geometry
  repetitions : Usize
  bindings : List Binding

def initial : State := ⟨none,⟨0,by decide⟩,[]⟩

def agrees (previous : Option Geometry) (current : Geometry) : Bool :=
  match previous with
  | none => true
  | some geometry => decide (geometry = current)

def step (registry : List Parameters) (helper : Parameters) (state : State) (request : Request) : Option State :=
  (gather registry request.terminal.sourceSlots).bind (fun sources =>
    (NativeLookupBindGeometry.bind request.columns request.terminal.logicalLength helper sources).bind (fun geometry =>
      if agrees state.geometry (key geometry) then
        (addRepetitions state.repetitions request.repetitions).map (fun repetitions =>
          ⟨some (key geometry),repetitions,state.bindings ++ [⟨request,sources,geometry⟩]⟩)
      else none))

def loop (registry : List Parameters) (helper : Parameters) : State → List Request → Option State
  | state, [] => some state
  | state, request :: tail => (step registry helper state request).bind (fun next => loop registry helper next tail)

structure Output where
  geometry : Geometry
  repetitions : Usize
  bindings : List Binding

def preflight (registry : List Parameters) (helper : Parameters) (requests : List Request) : Option Output :=
  if registryDimensions registry requests && uniform registry then
    (loop registry helper initial requests).bind (fun state => state.geometry.map (fun geometry =>
      ⟨geometry,state.repetitions,state.bindings⟩))
  else none

structure Bound (registry : List Parameters) (helper : Parameters) (binding : Binding) : Prop where
  sources : gather registry binding.request.terminal.sourceSlots = some binding.sources
  geometry : NativeLookupBindGeometry.bind binding.request.columns binding.request.terminal.logicalLength helper binding.sources = some binding.geometry

structure Valid (registry : List Parameters) (helper : Parameters) (state : State) : Prop where
  repetitions : state.repetitions.val = (state.bindings.map (fun binding => binding.request.repetitions)).sum
  bound : ∀ binding ∈ state.bindings, Bound registry helper binding
  common : ∀ binding ∈ state.bindings, state.geometry = some (key binding.geometry)

theorem gather_related (registry : List Parameters) (slots : List ℕ) (sources : List Parameters)
    (success : gather registry slots = some sources) : List.Forall₂ (fun slot source => registry[slot]? = some source) slots sources := by
  induction slots generalizing sources with
  | nil => have same : [] = sources := Option.some.inj success; subst sources; exact .nil
  | cons slot tail ih =>
    cases found : registry[slot]? with
    | none => simp only [gather, found, Option.bind_none] at success; contradiction
    | some source =>
      cases rest : gather registry tail with
      | none => simp only [gather, found, Option.bind_some, rest, Option.map_none] at success; contradiction
      | some remaining =>
        have same : source :: remaining = sources := Option.some.inj
          (by simpa only [gather, found, Option.bind_some, rest, Option.map_some] using success)
        rw [← same]
        exact .cons found (ih remaining rest)

theorem registryDimensions_iff (registry : List Parameters) (requests : List Request) :
    registryDimensions registry requests = true ↔ registry ≠ [] ∧ requests ≠ [] ∧
      ∀ request ∈ requests, request.terminal.sourceSlots.length = request.columns ∧
        ∀ slot ∈ request.terminal.sourceSlots, slot < registry.length := by
  simp only [registryDimensions, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

theorem uniform_spec (registry : List Parameters) (success : uniform registry = true) :
    ∃ first, registry.head? = some first ∧ ∀ source ∈ registry, source = first := by
  cases head : registry.head? with
  | none => simp only [uniform, head, Bool.false_eq_true] at success
  | some first =>
    refine ⟨first,rfl,?_⟩
    simpa only [uniform, head, List.all_eq_true, decide_eq_true_eq] using success

theorem step_spec (registry : List Parameters) (helper : Parameters) (state : State) (request : Request) (next : State)
    (success : step registry helper state request = some next) :
    ∃ sources geometry, Bound registry helper ⟨request,sources,geometry⟩ ∧ agrees state.geometry (key geometry) = true ∧
      next.geometry = some (key geometry) ∧ next.repetitions.val = state.repetitions.val + request.repetitions ∧
      next.bindings = state.bindings ++ [⟨request,sources,geometry⟩] := by
  rcases Option.bind_eq_some_iff.mp success with ⟨sources,gathered,rest⟩
  rcases Option.bind_eq_some_iff.mp rest with ⟨geometry,bound,rest⟩
  by_cases good : agrees state.geometry (key geometry) = true
  · rw [ite_eq_left good] at rest
    cases added : addRepetitions state.repetitions request.repetitions with
    | none => simp only [added, Option.map_none] at rest; contradiction
    | some count =>
      have same : State.mk (some (key geometry)) count (state.bindings ++ [⟨request,sources,geometry⟩]) = next :=
        Option.some.inj (by simpa only [added, Option.map_some] using rest)
      rw [← same]
      refine ⟨sources,geometry,⟨gathered,bound⟩,good,rfl,?_,rfl⟩
      unfold addRepetitions at added
      split at added
      · exact congrArg Fin.val (Option.some.inj added).symm
      · contradiction
  · rw [ite_eq_right good] at rest; contradiction

theorem step_valid (registry : List Parameters) (helper : Parameters) (state : State) (request : Request) (next : State)
    (valid : Valid registry helper state) (success : step registry helper state request = some next) : Valid registry helper next := by
  obtain ⟨sources,geometry,bound,agree,common,repetitions,bindings⟩ := step_spec registry helper state request next success
  refine ⟨?_,?_,?_⟩
  · rw [repetitions,bindings,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,valid.repetitions]
  · intro binding member
    rw [bindings] at member
    rcases List.mem_append.mp member with old | new
    · exact valid.bound binding old
    · have same := List.mem_singleton.mp new; subst binding; exact bound
  · intro binding member
    rw [bindings] at member
    rcases List.mem_append.mp member with old | new
    · have previous := valid.common binding old
      have equal : key binding.geometry = key geometry := by
        simpa only [previous,agrees,decide_eq_true_eq] using agree
      exact common.trans (congrArg some equal.symm)
    · have same := List.mem_singleton.mp new; subst binding; exact common

theorem loop_valid (registry : List Parameters) (helper : Parameters) (state : State) (requests : List Request) (result : State)
    (valid : Valid registry helper state) (success : loop registry helper state requests = some result) : Valid registry helper result := by
  induction requests generalizing state with
  | nil => have same : state = result := Option.some.inj success; rw [← same]; exact valid
  | cons request tail ih =>
    rcases Option.bind_eq_some_iff.mp success with ⟨next,advanced,rest⟩
    exact ih next (step_valid registry helper state request next valid advanced) rest

theorem loop_requests (registry : List Parameters) (helper : Parameters) (state : State) (requests : List Request) (result : State)
    (success : loop registry helper state requests = some result) :
    result.bindings.map Binding.request = state.bindings.map Binding.request ++ requests := by
  induction requests generalizing state with
  | nil => have same : state = result := Option.some.inj success; rw [← same,List.append_nil]
  | cons request tail ih =>
    rcases Option.bind_eq_some_iff.mp success with ⟨next,advanced,rest⟩
    obtain ⟨_,_,_,_,_,_,bindings⟩ := step_spec registry helper state request next advanced
    rw [ih next rest,bindings,List.map_append,List.map_singleton,List.append_assoc,List.singleton_append]

structure Accepted (registry : List Parameters) (helper : Parameters) (requests : List Request) (output : Output) : Prop where
  dimensions : registry ≠ [] ∧ requests ≠ [] ∧ ∀ request ∈ requests,
    request.terminal.sourceSlots.length = request.columns ∧ ∀ slot ∈ request.terminal.sourceSlots, slot < registry.length
  uniform : ∃ first, registry.head? = some first ∧ ∀ source ∈ registry, source = first
  order : output.bindings.map Binding.request = requests
  repetitions : output.repetitions.val = (requests.map Request.repetitions).sum
  bound : ∀ binding ∈ output.bindings, Bound registry helper binding
  common : ∀ binding ∈ output.bindings, key binding.geometry = output.geometry

theorem preflight_spec (registry : List Parameters) (helper : Parameters) (requests : List Request) (output : Output)
    (success : preflight registry helper requests = some output) : Accepted registry helper requests output := by
  unfold preflight at success
  by_cases good : (registryDimensions registry requests && uniform registry) = true
  · rw [ite_eq_left good] at success
    have checks : registryDimensions registry requests = true ∧ uniform registry = true := by
      simpa only [Bool.and_eq_true] using good
    rcases Option.bind_eq_some_iff.mp success with ⟨state,processed,rest⟩
    cases geometry : state.geometry with
    | none => simp only [geometry, Option.map_none] at rest; contradiction
    | some dimensions =>
      have same : Output.mk dimensions state.repetitions state.bindings = output := Option.some.inj
        (by simpa only [geometry,Option.map_some] using rest)
      rw [← same]
      have valid := loop_valid registry helper initial requests state
        ⟨rfl,by simp [initial],by simp [initial]⟩ processed
      have order := loop_requests registry helper initial requests state processed
      simp only [initial,List.map_nil,List.nil_append] at order
      refine ⟨(registryDimensions_iff registry requests).mp checks.1,uniform_spec registry checks.2,order,?_,valid.bound,?_⟩
      · rw [valid.repetitions,← order,List.map_map]
        rfl
      · intro binding member
        have common := valid.common binding member
        rw [geometry] at common
        exact (Option.some.inj common).symm
  · rw [ite_eq_right good] at success; contradiction

/-- Every original request has a computed binding at the one accepted
geometry. Alias/repeated slots retain their original ordered copies. -/
theorem request_geometry (registry : List Parameters) (helper : Parameters) (requests : List Request) (output : Output)
    (success : preflight registry helper requests = some output) (request : Request) (member : request ∈ requests) :
    ∃ binding ∈ output.bindings, binding.request = request ∧
      List.Forall₂ (fun slot source => registry[slot]? = some source) request.terminal.sourceSlots binding.sources ∧
      binding.geometry.numVariables = output.geometry.1 ∧ binding.geometry.width = output.geometry.2 ∧
      request.terminal.logicalLength.val ≤ 2^output.geometry.1.val ∧ output.geometry.1.val < 64 := by
  have accepted := preflight_spec registry helper requests output success
  rw [← accepted.order] at member
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  have bound := accepted.bound binding present
  have geometry := accepted.common binding present
  have variablesEq := congrArg Prod.fst geometry
  have widthEq := congrArg Prod.snd geometry
  have spec := NativeLookupBindGeometry.bind_spec _ _ _ _ _ bound.geometry
  refine ⟨binding,present,same,?_,variablesEq,widthEq,?_,?_⟩
  · rw [← same]; exact gather_related registry binding.request.terminal.sourceSlots binding.sources bound.sources
  · rw [← same,← variablesEq]; exact spec.logical
  · rw [← variablesEq]; exact spec.shift

theorem gather_members (registry : List Parameters) (slots : List ℕ) (sources : List Parameters)
    (success : gather registry slots = some sources) : ∀ source ∈ sources, source ∈ registry := by
  have related := gather_related registry slots sources success
  clear success
  induction related with
  | nil => simp
  | @cons slot source tail remaining found related ih =>
    intro value member
    rcases List.mem_cons.mp member with same | rest
    · subst value
      obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp found
      rw [← same]
      exact List.getElem_mem bound
    · exact ih value rest

private theorem head_mem {α : Type} (values : List α) (value : α) (found : values.head? = some value) : value ∈ values := by
  cases values with
  | nil => contradiction
  | cons first tail => have same : first = value := Option.some.inj found; rw [← same]; exact List.mem_cons_self

/-- The scalar query's source variables and lane width come from the original
registry head; helper width remains independently permitted to be three. -/
theorem registry_geometry (registry : List Parameters) (helper : Parameters) (requests : List Request) (output : Output)
    (success : preflight registry helper requests = some output) :
    ∃ first, registry.head? = some first ∧ (∀ source ∈ registry, source = first) ∧
      output.geometry.2 = first.width ∧
      output.geometry.1.val = first.numVariables.val + NativeScalarQueryShape.laneBits first.width.val ∧
      helper.numVariables = output.geometry.1 ∧ (helper.width = output.geometry.2 ∨ helper.width.val = 3) := by
  have accepted := preflight_spec registry helper requests output success
  obtain ⟨first,head,uniform⟩ := accepted.uniform
  have nonempty : output.bindings ≠ [] := by
    intro empty
    have order := accepted.order
    rw [empty,List.map_nil] at order
    exact accepted.dimensions.2.1 order.symm
  obtain ⟨binding,member⟩ := List.exists_mem_of_ne_nil output.bindings nonempty
  have bound := accepted.bound binding member
  have geometry := accepted.common binding member
  have variablesEq := congrArg Prod.fst geometry
  have widthEq := congrArg Prod.snd geometry
  have spec := NativeLookupBindGeometry.bind_spec _ _ _ _ _ bound.geometry
  obtain ⟨localFirst,localHead,localWidth,_,_,localVariables,_⟩ := spec.first
  have same := uniform localFirst (gather_members registry binding.request.terminal.sourceSlots binding.sources bound.sources
    localFirst (head_mem binding.sources localFirst localHead))
  subst localFirst
  refine ⟨first,head,uniform,?_,?_,?_,?_⟩
  · exact widthEq.symm.trans localWidth
  · rw [← variablesEq]; exact localVariables
  · exact spec.helperVariables.trans variablesEq
  · rcases spec.helperWidth with equal | degree
    · exact Or.inl (equal.trans widthEq)
    · exact Or.inr degree

theorem tags_length {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request) :
    (NativeSharedLookupStatement.tags fits requests).length = ((List.ofFn requests).map Request.repetitions).sum := by
  simp only [NativeSharedLookupStatement.tags,List.length_flatten,List.map_ofFn,List.length_ofFn,Function.comp_def]

theorem repetitions_tags {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → Request)
    (registry : List Parameters) (helper : Parameters) (output : Output)
    (success : preflight registry helper (List.ofFn requests) = some output) :
    output.repetitions.val = (NativeSharedLookupStatement.tags fits requests).length := by
  rw [tags_length]
  exact (preflight_spec registry helper (List.ofFn requests) output success).repetitions

theorem geometry_bounds (registry : List Parameters) (helper : Parameters) (requests : List Request) (output : Output)
    (success : preflight registry helper requests = some output) :
    output.geometry.1.val < 64 ∧ ∀ request ∈ requests, request.terminal.logicalLength.val ≤ 2^output.geometry.1.val := by
  have accepted := preflight_spec registry helper requests output success
  obtain ⟨request,member⟩ := List.exists_mem_of_ne_nil requests accepted.dimensions.2.1
  obtain ⟨_,_,_,_,_,_,_,shift⟩ := request_geometry registry helper requests output success request member
  refine ⟨shift,?_⟩
  intro request member
  obtain ⟨_,_,_,_,_,_,logical,_⟩ := request_geometry registry helper requests output success request member
  exact logical

end FormalProof4FHE.HasteBoots.NativeSharedLookupPreflight
