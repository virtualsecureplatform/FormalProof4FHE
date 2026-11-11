module
public import FormalProof4FHE.HasteBoots.LookupReceiptLabels
@[expose] public section

/-! Every actual equality reader and retained point uses the equality label,
separating its receipt suffix from lookup compression/reciprocal groups. -/
namespace FormalProof4FHE.HasteBoots.EqualityReceiptLabels
open InputIndexedOracle (World)
noncomputable section

def Labels {count : ℕ} {K : Type} (machine : NativeLookupEquality.Machine count K) : Prop :=
  (∀ field, machine.active = some field → field.phase.label = NativeLookupEquality.pointLabel) ∧
    ∀ draw ∈ machine.draws, draw.coefficients.phase.label = NativeLookupEquality.pointLabel

variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

omit [Field K] [Algebra (ZMod p) K] in
theorem initial (count : ℕ) (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) : Labels (NativeLookupEquality.initial (K := K) count transcript roots fits) := by
  constructor
  · intro field impossible; contradiction
  · intro draw impossible; contradiction

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (valid : Labels machine) :
    Labels (NativeLookupEquality.tickExecute basis w machine world).1 := by
  by_cases complete : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,complete,ite_true] using valid
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,Labels]
      refine ⟨?_,valid.2⟩
      intro field same
      exact Option.some.inj same ▸ rfl
    | some field =>
      have label := LookupReceiptLabels.drive_label p 1 field world
      cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
      | suspended next =>
        rw [result] at label
        have nextLabel : next.phase.label = NativeLookupEquality.pointLabel := label.trans (valid.1 field active)
        simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,Labels]
        refine ⟨?_,valid.2⟩
        intro field same
        exact Option.some.inj same ▸ nextLabel
      | finished next transcript =>
        rw [result] at label
        have nextLabel : next.phase.label = NativeLookupEquality.pointLabel := label.trans (valid.1 field active)
        simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,Labels]
        constructor
        · intro field impossible; contradiction
        · intro draw member
          rcases List.mem_append.mp member with old | added
          · exact valid.2 draw old
          · obtain rfl := List.mem_singleton.mp added
            exact nextLabel

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (valid : Labels machine) :
    Labels (NativeLookupEquality.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w machine world valid)

theorem request (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) (world : World) :
    Labels (OracleProgram.run (NativeLookupEquality.request basis w count fuel transcript roots fits) world).run.1 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  exact execute basis w fuel _ world (initial count transcript roots fits)

end
end FormalProof4FHE.HasteBoots.EqualityReceiptLabels
