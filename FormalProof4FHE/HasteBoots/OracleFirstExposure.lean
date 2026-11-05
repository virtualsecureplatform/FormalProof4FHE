module

public import FormalProof4FHE.HasteBoots.CachedOracleResponse
@[expose] public section

/-! Earliest returned-coordinate exposure in the complete raw observation
log. Starts and empty reads reveal no coordinates. This view never filters
out arbitrary, duplicate, unclassified or rejected-query observations. The
seed specialization covers all64 positions under the exact complete input,
without assuming that a verifier initiated the first read. Root extraction
from native input framing and descendant/parent linkage remain open. -/
namespace FormalProof4FHE.HasteBoots.OracleFirstExposure
open InputIndexedOracle (Coordinate)
open NativeTranscript (Observation)
open scoped Classical

noncomputable def locate : List Observation → Finset Coordinate → Option ℕ
  | [], _ => none
  | entry::rest, relevant =>
    if Disjoint (ObservationReplay.coordinates entry) relevant then
      (locate rest relevant).map Nat.succ else some 0

theorem locate_none (log : List Observation) (relevant : Finset Coordinate) :
    locate log relevant = none ↔ Disjoint (ObservationReplay.footprint log) relevant := by
  induction log with
  | nil => simp [locate,ObservationReplay.footprint]
  | cons entry rest ih =>
    simp only [locate,ObservationReplay.footprint,List.toFinset_cons,Finset.biUnion_insert,
      Finset.disjoint_union_left]
    split <;> simp_all [ObservationReplay.footprint]

theorem locate_some (log : List Observation) (relevant : Finset Coordinate) (index : ℕ) :
    locate log relevant = some index ↔ ∃ before entry after,
      log = before++entry::after ∧ before.length = index ∧
      Disjoint (ObservationReplay.footprint before) relevant ∧
      ¬ Disjoint (ObservationReplay.coordinates entry) relevant := by
  induction log generalizing index with
  | nil => simp [locate]
  | cons entry rest ih =>
    by_cases disjoint : Disjoint (ObservationReplay.coordinates entry) relevant
    · simp only [locate,disjoint,ite_true]
      constructor
      · intro found
        obtain ⟨position,tailFound,equalIndex⟩ := Option.map_eq_some_iff.mp found
        subst index
        obtain ⟨before,head,after,split,length,earlier,hit⟩ := (ih position).mp tailFound
        refine ⟨entry::before,head,after,?_,by simp [length],?_,hit⟩
        · simp [split]
        · simpa [ObservationReplay.footprint,Finset.disjoint_union_left] using And.intro disjoint earlier
      · rintro ⟨before,head,after,split,length,earlier,hit⟩
        cases before with
        | nil => simp only [List.nil_append,List.cons.injEq] at split; exact False.elim (hit (split.1 ▸ disjoint))
        | cons first before =>
          have parts := List.cons.inj split
          have headEq := parts.1
          subst first
          have tailEarlier : Disjoint (ObservationReplay.footprint before) relevant := by
            simpa [ObservationReplay.footprint,Finset.disjoint_union_left,disjoint] using earlier
          have tailFound := (ih before.length).mpr ⟨before,head,after,parts.2,rfl,tailEarlier,hit⟩
          rw [tailFound]
          simpa using congrArg some length
    · simp only [locate,disjoint,ite_false,Option.some.injEq]
      constructor
      · intro equal
        exact ⟨[],entry,rest,rfl,equal,by simp [ObservationReplay.footprint],disjoint⟩
      · rintro ⟨before,head,after,split,length,earlier,hit⟩
        cases before with
        | nil => simpa using length
        | cons first before =>
          have parts := List.cons.inj split
          have headEq := parts.1
          subst first
          have firstDisjoint : Disjoint (ObservationReplay.coordinates entry) relevant := by
            exact ((show Disjoint (ObservationReplay.coordinates entry) relevant ∧
              Disjoint (ObservationReplay.footprint before) relevant by
                simpa [ObservationReplay.footprint,Finset.disjoint_union_left] using earlier)).1
          exact False.elim (disjoint firstDisjoint)


theorem locate_append (first later : List Observation) (relevant : Finset Coordinate) :
    locate (first++later) relevant = match locate first relevant with
      | some index => some index
      | none => (locate later relevant).map (fun index => first.length+index) := by
  induction first with
  | nil => simp [locate]
  | cons entry rest ih =>
    simp only [List.cons_append,locate]
    split
    · rw [ih]
      cases early : locate rest relevant <;> cases late : locate later relevant <;>
        simp [Nat.add_assoc,Nat.add_comm]
    · rfl

def seedCoordinates (input : InputIndexedOracle.Input) : Finset Coordinate :=
  Finset.univ.image (CachedOracleResponse.shakeCoordinates input 0 64)

theorem seed_none (log : List Observation) (input : InputIndexedOracle.Input) :
    locate log (seedCoordinates input) = none ↔
      ∀ position : Fin 64, (.inl (input,position.val) : Coordinate) ∉ ObservationReplay.footprint log := by
  rw [locate_none,disjoint_comm,Finset.disjoint_left]
  simp only [seedCoordinates,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro apart position
    exact apart (by exact ⟨position,by simp [CachedOracleResponse.shakeCoordinates]⟩)
  · intro apart coordinate member
    obtain ⟨position,rfl⟩ := member
    simpa [CachedOracleResponse.shakeCoordinates] using apart position

theorem seed_before_fresh (log : List Observation) (input : InputIndexedOracle.Input) (index : ℕ)
    (first : locate log (seedCoordinates input) = some index) :
    ∀ position : Fin 64, (.inl (input,position.val) : Coordinate) ∉
      ObservationReplay.footprint (log.take index) := by
  obtain ⟨before,entry,after,split,length,earlier,hit⟩ := (locate_some log _ index).mp first
  rw [split,← length,List.take_left]
  intro position member
  exact Finset.disjoint_left.mp earlier member (by simp [seedCoordinates,CachedOracleResponse.shakeCoordinates])

theorem locate_preserved (first later : List Observation) (relevant : Finset Coordinate) (index : ℕ)
    (found : locate first relevant = some index) : locate (first++later) relevant = some index := by
  rw [locate_append,found]


/-- An exposure is a real position in the complete raw log. -/
theorem locate_lt (log : List Observation) (relevant : Finset Coordinate) (index : ℕ)
    (found : locate log relevant = some index) : index < log.length := by
  obtain ⟨before,entry,after,split,length,earlier,hit⟩ := (locate_some log relevant index).mp found
  rw [split,List.length_append,List.length_cons,← length]
  omega

end FormalProof4FHE.HasteBoots.OracleFirstExposure

