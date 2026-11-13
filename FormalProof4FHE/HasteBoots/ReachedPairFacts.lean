module
public import FormalProof4FHE.HasteBoots.DependentStageSupport
@[expose] public section

/-! Compose operational reachability facts across supported optional-result
prefixes, without inspecting or expanding their probability computations. -/
namespace FormalProof4FHE.HasteBoots.ReachedPairFacts
open OracleSpec OracleComp

/-- A later reached stage exposes a stored predecessor. Apply the predecessor's
actual reachability theorem to that same supported pair, retaining both facts. -/
theorem extend {Previous Earlier Later : Type}
    (earlier : ProbComp (Previous × Option Earlier))
    (later : ProbComp ((Previous × Option Earlier) × Option Later))
    {Gate : Earlier → Prop} {Payload : Later → Earlier → Prop} {Facts : Previous → Earlier → Prop}
    (reachedLater : ∀ before returned, (before,some returned) ∈ support later →
      ∃ selected, before.2 = some selected ∧ Gate selected ∧ before ∈ support earlier ∧ Payload returned selected)
    (reachedEarlier : ∀ previous selected, (previous,some selected) ∈ support earlier → Facts previous selected)
    (before : Previous × Option Earlier) (returned : Later)
    (supported : (before,some returned) ∈ support later) :
    ∃ selected, before.2 = some selected ∧ Gate selected ∧ before ∈ support earlier ∧
      (Payload returned selected ∧ Facts before.1 selected) := by
  obtain ⟨selected,present,accepted,member,payload⟩ := reachedLater before returned supported
  have same : before = (before.1,some selected) := Prod.ext rfl present
  have previousSupported : (before.1,some selected) ∈ support earlier := same ▸ member
  exact ⟨selected,present,accepted,member,payload,reachedEarlier before.1 selected previousSupported⟩

end FormalProof4FHE.HasteBoots.ReachedPairFacts
