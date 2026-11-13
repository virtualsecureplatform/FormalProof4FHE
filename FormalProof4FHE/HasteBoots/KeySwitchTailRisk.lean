module
public import FormalProof4FHE.HasteBoots.ReachedPairFacts
@[expose] public section

/-! The optional-result risk union in the complete key-switch tail. Lookup
failure contributes only together with the actual comparison acceptance flag. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchTailRisk
open OracleSpec OracleComp

abbrev BeforeInput (Prefix Acc MonoNTT Mono : Type) :=
  ((Prefix × Option Acc) × Option MonoNTT) × Option Mono

abbrev BeforeComparison (Prefix Acc MonoNTT Mono Known NTT Product Reconstruction : Type) :=
  (((BeforeInput Prefix Acc MonoNTT Mono × Option Known) × Option NTT) × Option Product) ×
    Option Reconstruction

/-- Extend an earlier risk by a risk in the child actually stored by this run. -/
def lift {Before Child : Type} (earlier : Before → Prop) (childRisk : Child → Prop)
    (outcome : Before × Option Child) : Prop :=
  earlier outcome.1 ∨ ∃ child, outcome.2 = some child ∧ childRisk child

/-- Known-input risk uses the stored monomial product and accumulator context. -/
def inputRisk {Prefix Acc MonoNTT Mono Known : Type}
    (earlier : BeforeInput Prefix Acc MonoNTT Mono → Prop)
    (knownRisk : Mono → Acc → Known → Prop)
    (outcome : BeforeInput Prefix Acc MonoNTT Mono × Option Known) : Prop :=
  earlier outcome.1 ∨ ∃ mono acc known, outcome.1.2 = some mono ∧
    outcome.1.1.1.2 = some acc ∧ outcome.2 = some known ∧ knownRisk mono acc known

/-- The same nested union used by the complete rectangular PBS bound. -/
def Risk {Prefix Acc MonoNTT Mono Known NTT Product Reconstruction Comparison : Type}
    (earlier : BeforeInput Prefix Acc MonoNTT Mono → Prop)
    (knownRisk : Mono → Acc → Known → Prop) (nttRisk : NTT → Prop)
    (productRisk : Product → Prop) (reconstructionRisk : Reconstruction → Prop)
    (lookupFalse accepted : Comparison → Prop)
    (outcome : BeforeComparison Prefix Acc MonoNTT Mono Known NTT Product Reconstruction ×
      Option Comparison) : Prop :=
  lift (lift (lift (lift (inputRisk earlier knownRisk) nttRisk) productRisk) reconstructionRisk)
    (fun compared => lookupFalse compared ∧ accepted compared) outcome

/-- Inject the actual selected operation failures into the complete risk union.
No earlier-stage failure or comparison acceptance is inferred from a return. -/
theorem of_selected_failures
    {Prefix Acc MonoNTT Mono Known NTT Product Reconstruction Comparison : Type}
    (earlier : BeforeInput Prefix Acc MonoNTT Mono → Prop)
    (knownRisk : Mono → Acc → Known → Prop) (nttRisk : NTT → Prop)
    (productRisk : Product → Prop) (reconstructionRisk : Reconstruction → Prop)
    (lookupFalse accepted : Comparison → Prop)
    (before : BeforeComparison Prefix Acc MonoNTT Mono Known NTT Product Reconstruction)
    (compared : Comparison) (acc : Acc) (mono : Mono) (known : Known) (ntt : NTT)
    (product : Product) (reconstructed : Reconstruction)
    (accPresent : before.1.1.1.1.1.1.2 = some acc)
    (monoPresent : before.1.1.1.1.2 = some mono)
    (knownPresent : before.1.1.1.2 = some known)
    (nttPresent : before.1.1.2 = some ntt)
    (productPresent : before.1.2 = some product)
    (reconstructionPresent : before.2 = some reconstructed)
    (passed : accepted compared) {Bad : Prop}
    (failure : lookupFalse compared ∨ reconstructionRisk reconstructed ∨ knownRisk mono acc known ∨
      nttRisk ntt ∨ productRisk product ∨ Bad) :
    Risk earlier knownRisk nttRisk productRisk reconstructionRisk lookupFalse accepted
      (before,some compared) ∨ Bad := by
  rcases failure with lookup | reconstruction | knownFailure | nttFailure | productFailure | bad
  · exact Or.inl (Or.inr ⟨compared,rfl,lookup,passed⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨reconstructed,reconstructionPresent,reconstruction⟩))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨mono,acc,known,monoPresent,accPresent,knownPresent,knownFailure⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ntt,nttPresent,nttFailure⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨product,productPresent,productFailure⟩)))
  · exact Or.inr bad

/-- Canonical increment coverage, conditioned on the real final acceptance
flag, is correctness or the exact complete risk union or final history failure. -/
theorem correct_or_risk
    {Prefix Acc MonoNTT Mono Known NTT Product Reconstruction Comparison : Type}
    (earlier : BeforeInput Prefix Acc MonoNTT Mono → Prop)
    (knownRisk : Mono → Acc → Known → Prop) (nttRisk : NTT → Prop)
    (productRisk : Product → Prop) (reconstructionRisk : Reconstruction → Prop)
    (lookupFalse accepted : Comparison → Prop)
    (before : BeforeComparison Prefix Acc MonoNTT Mono Known NTT Product Reconstruction)
    (compared : Comparison) (acc : Acc) (mono : Mono) (known : Known) (ntt : NTT)
    (product : Product) (reconstructed : Reconstruction)
    (accPresent : before.1.1.1.1.1.1.2 = some acc)
    (monoPresent : before.1.1.1.1.2 = some mono)
    (knownPresent : before.1.1.1.2 = some known)
    (nttPresent : before.1.1.2 = some ntt)
    (productPresent : before.1.2 = some product)
    (reconstructionPresent : before.2 = some reconstructed)
    (passed : accepted compared) {Correct Bad : Prop}
    (coverage : Correct ∨ lookupFalse compared ∨ reconstructionRisk reconstructed ∨
      knownRisk mono acc known ∨ nttRisk ntt ∨ productRisk product ∨ Bad) :
    Correct ∨ Risk earlier knownRisk nttRisk productRisk reconstructionRisk lookupFalse accepted
      (before,some compared) ∨ Bad := by
  rcases coverage with correct | failures
  · exact Or.inl correct
  · exact Or.inr (of_selected_failures earlier knownRisk nttRisk productRisk reconstructionRisk
      lookupFalse accepted before compared acc mono known ntt product reconstructed accPresent
      monoPresent knownPresent nttPresent productPresent reconstructionPresent passed failures)

/-- Enlarging only the predecessor event preserves every selected tail risk
and the final comparison's acceptance condition. -/
theorem mono_earlier
    {Prefix Acc MonoNTT Mono Known NTT Product Reconstruction Comparison : Type}
    {earlier later : BeforeInput Prefix Acc MonoNTT Mono → Prop}
    (knownRisk : Mono → Acc → Known → Prop) (nttRisk : NTT → Prop)
    (productRisk : Product → Prop) (reconstructionRisk : Reconstruction → Prop)
    (lookupFalse accepted : Comparison → Prop)
    (subset : ∀ before, earlier before → later before)
    (outcome : BeforeComparison Prefix Acc MonoNTT Mono Known NTT Product Reconstruction ×
      Option Comparison)
    (failure : Risk earlier knownRisk nttRisk productRisk reconstructionRisk lookupFalse accepted outcome) :
    Risk later knownRisk nttRisk productRisk reconstructionRisk lookupFalse accepted outcome := by
  rcases failure with ((((early | known) | ntt) | product) | reconstruction) | comparison
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (subset _ early)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr known))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ntt)))
  · exact Or.inl (Or.inl (Or.inr product))
  · exact Or.inl (Or.inr reconstruction)
  · exact Or.inr comparison

/-- The semantic tail event embeds in the complete predecessor-and-tail
probability event without adding a union factor or another history charge. -/
theorem probability_mono_earlier
    {Prefix Acc MonoNTT Mono Known NTT Product Reconstruction Comparison : Type}
    {earlier later : BeforeInput Prefix Acc MonoNTT Mono → Prop}
    (knownRisk : Mono → Acc → Known → Prop) (nttRisk : NTT → Prop)
    (productRisk : Product → Prop) (reconstructionRisk : Reconstruction → Prop)
    (lookupFalse accepted : Comparison → Prop)
    (subset : ∀ before, earlier before → later before)
    (experiment : ProbComp
      (BeforeComparison Prefix Acc MonoNTT Mono Known NTT Product Reconstruction × Option Comparison))
    (bad : BeforeComparison Prefix Acc MonoNTT Mono Known NTT Product Reconstruction × Option Comparison → Prop) :
    Pr{let outcome ← experiment}[
      Risk earlier knownRisk nttRisk productRisk reconstructionRisk lookupFalse accepted outcome ∨ bad outcome] ≤
    Pr{let outcome ← experiment}[
      Risk later knownRisk nttRisk productRisk reconstructionRisk lookupFalse accepted outcome ∨ bad outcome] := by
  apply prEvent_mono
  intro outcome failure
  exact failure.elim
    (fun risky => Or.inl (mono_earlier knownRisk nttRisk productRisk reconstructionRisk
      lookupFalse accepted subset outcome risky)) Or.inr

end FormalProof4FHE.HasteBoots.KeySwitchTailRisk
