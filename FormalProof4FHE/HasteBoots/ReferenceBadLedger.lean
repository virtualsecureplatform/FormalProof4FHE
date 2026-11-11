module
public import FormalProof4FHE.HasteBoots.JobReferenceSelection
@[expose] public section

/-! The reference-selection remainder is the union of existing shared events.
Its posterior average retains the real root/hash probability and each lifetime
ledger once. No per-factor, per-reference or successful-mass multiplier appears. -/
namespace FormalProof4FHE.HasteBoots.ReferenceBadLedger
open InputIndexedOracle (World law)
open OracleProgram (Program runPrefix)
open NativeRootMessage (Digest)
open JobReferenceSelection (Bad)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

theorem bad_iff {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (world : World) :
    Bad program position dummy world ↔
      NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2 ∨ ProgramParentSeedCollision.Bad program world ∨
        ProgramContextTarget.Bad program world ∨ ProgramReceiptCoverage.Bad program world ∨ ProgramReceiptCollision.Bad program world := by
  constructor
  · intro notGood
    by_cases root : NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2
    · exact Or.inl root
    by_cases parent : ProgramParentSeedCollision.Bad program world
    · exact Or.inr (Or.inl parent)
    by_cases context : ProgramContextTarget.Bad program world
    · exact Or.inr (Or.inr (Or.inl context))
    by_cases receipt : ProgramReceiptCoverage.Bad program world
    · exact Or.inr (Or.inr (Or.inr (Or.inl receipt)))
    by_cases collision : ProgramReceiptCollision.Bad program world
    · exact Or.inr (Or.inr (Or.inr (Or.inr collision)))
    exact False.elim (notGood ⟨parent,root,context,receipt,collision⟩)
  · rintro (root | parent | context | receipt | collision) good
    · exact good.root root
    · exact good.parent parent
    · exact good.context context
    · exact good.receipt receipt
    · exact good.collision collision

theorem receipt_measurable {A : Type} (program : Program A) : MeasurableSet {world | ProgramReceiptCoverage.Bad program world} := by
  have union : {world | ProgramReceiptCoverage.Bad program world} = ⋃ position : ℕ,
      {world | FreshReceiptTargetRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := by ext world; simp [ProgramReceiptCoverage.Bad]
  rw [union]
  exact MeasurableSet.iUnion (fun position => FreshReceiptTargetRisk.event_measurable OracleProgramMachine.step (OracleProgram.prefix_replay position program))

theorem parent_measurable {A : Type} (program : Program A) : MeasurableSet {world | ProgramParentSeedCollision.Bad program world} := by
  have union : {world | ProgramParentSeedCollision.Bad program world} = ⋃ position : ℕ,
      {world | ParentSeedCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := by ext world; simp [ProgramParentSeedCollision.Bad]
  rw [union]
  exact MeasurableSet.iUnion (fun position => ParentSeedCollisionRisk.event_measurable OracleProgramMachine.step (OracleProgram.prefix_replay position program))

theorem collision_measurable {A : Type} (program : Program A) : MeasurableSet {world | ProgramReceiptCollision.Bad program world} := by
  have union : {world | ProgramReceiptCollision.Bad program world} = ⋃ position : ℕ,
      {world | ReceiptCollisionRisk.event OracleProgramMachine.step (runPrefix position program world).run world} := by ext world; simp [ProgramReceiptCollision.Bad]
  rw [union]
  exact MeasurableSet.iUnion (fun position => ReceiptCollisionRisk.event_measurable OracleProgramMachine.step (OracleProgram.prefix_replay position program))

theorem root_measurable {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    MeasurableSet {world | NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2} := by
  apply OracleProgramHistory.event_measurable (OracleProgram.prefix_replay position program)
    (fun packet _ => NativeRootFamilyLifetime.Bad dummy packet.2)
  intro packet
  by_cases bad : NativeRootFamilyLifetime.Bad dummy packet.2 <;> simp [bad]

theorem measurable {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    MeasurableSet {world | Bad program position dummy world} := by
  simpa only [bad_iff,Set.ofPred_or] using (root_measurable program position dummy).union
    ((parent_measurable program).union ((ProgramContextTarget.bad_measurable program).union
      ((receipt_measurable program).union (collision_measurable program))))

def charge {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) : ENNReal :=
  law {world | NativeRootFamilyLifetime.Bad dummy (runPrefix position program world).run.2} +
    ((∫⁻ world, ProgramParentSeedCollision.totalCharge program world ∂law) +
      ((∫⁻ world, ProgramContextTarget.totalCharge program world ∂law) +
        ((∫⁻ world, ProgramReceiptCoverage.totalCharge program world ∂law) + ∫⁻ world, ProgramReceiptCollision.totalCharge program world ∂law)))

theorem bad_le {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    law {world | Bad program position dummy world} ≤ charge program position dummy := by
  simp only [bad_iff,Set.ofPred_or,charge]
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans
  apply add_le_add (ProgramParentSeedCollision.bad_le program)
  apply (measure_union_le _ _).trans
  apply add_le_add (ProgramContextTarget.bad_le program)
  exact (measure_union_le _ _).trans (add_le_add (ProgramReceiptCoverage.bad_le program) (ProgramReceiptCollision.bad_le program))

theorem averaged_bad_le {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) :
    (∫⁻ world, (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
      (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} ∂law) ≤
      charge program position dummy := by
  rw [← OracleHistoryComposition.average_event (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)) law _ (measurable program position dummy)]
  exact bad_le program position dummy

/-- Local fixed-reference kernel bounds compose with the retained posterior
bad mass at a fixed analysis prefix. Their native degree/PCS instantiation
remains an explicit separate obligation. -/
theorem event_le {A : Type} (program : Program A) (position : ℕ) (dummy : Digest) (event : Set World)
    (eventMeasurable : MeasurableSet event) (risk : ENNReal)
    (localBound : ∀ world,
      (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run}]) event ≤
      (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} + risk) :
    law event ≤ risk + charge program position dummy := by
  rw [OracleHistoryComposition.average_event (ParentFactorFiber.replay (OracleProgram.prefix_replay position program)) law event eventMeasurable]
  calc
    _ ≤ ∫⁻ world, risk + (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} ∂law := by
      apply lintegral_mono
      intro world
      simpa only [add_comm] using localBound world
    _ = risk + ∫⁻ world, (law[|{other | (ParentFactorFiber.extend (runPrefix position program) other).run =
        (ParentFactorFiber.extend (runPrefix position program) world).run}]) {other | Bad program position dummy other} ∂law := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ _ := add_le_add le_rfl (averaged_bad_le program position dummy)

end
end FormalProof4FHE.HasteBoots.ReferenceBadLedger
