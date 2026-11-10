module
public import FormalProof4FHE.HasteBoots.SingleOpeningRecoveredMatrix
public import FormalProof4FHE.HasteBoots.NativeFieldMatrixLaw
@[expose] public section

/-! The native Goldilocks coefficient vector is exactly the rectangular
lane-major matrix, including the complete-symbol source-row ordering. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFieldMatrix
open NativeGoldPcsExecution (Context)
open SingleOpeningRectangularData (Row)
open NativeFields (Goldilocks goldilocksModulus)
open OracleComp
noncomputable section

def count (ctx : Context) : ℕ := 2^ctx.parameters.leftVariables.val*ctx.parameters.width.val*ctx.parameters.width.val

def index (ctx : Context) : Fin ctx.parameters.width.val × Row ctx ≃ Fin (count ctx) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans
    (NativeFieldMatrixLaw.index ctx.parameters.width.val (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val))

def reshape (ctx : Context) (size : ℕ) (same : size = count ctx) :
    (Fin size → Goldilocks) ≃ (Fin ctx.parameters.width.val → Row ctx → Goldilocks) :=
  (Equiv.arrowCongr ((finCongr same).trans (index ctx).symm) (Equiv.refl Goldilocks)).trans (Equiv.curry _ _ _)

theorem reshape_apply (ctx : Context) (size : ℕ) (same : size = count ctx) (vector : Fin size → Goldilocks)
    (lane : Fin ctx.parameters.width.val) (row : Row ctx) :
    reshape ctx size same vector lane row = vector ⟨lane.val*(2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)+
      (row.1.val*ctx.parameters.width.val+row.2.val),by
        have bound := ((index ctx) (lane,row)).isLt
        rw [same]
        change (row.2.val+ctx.parameters.width.val*row.1.val)+
          (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)*lane.val < count ctx at bound
        convert bound using 1; ring⟩ := by
  change vector ⟨(row.2.val+ctx.parameters.width.val*row.1.val)+
    (2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)*lane.val,_⟩ = _
  congr 1
  apply Fin.ext
  ring

theorem uniform_reshape (ctx : Context) (size : ℕ) (same : size = count ctx)
    (event : (Fin ctx.parameters.width.val → Row ctx → Goldilocks) → Prop) :
    Pr{let vector ← $ᵗ (Fin size → Goldilocks)}[event (reshape ctx size same vector)] =
      Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[event matrix] :=
  SampleableType.prEvent_uniformSample_equiv (reshape ctx size same) event

theorem project_random (ctx : Context) (size : ℕ) (same : size = count ctx) (state : NativeFieldVector.State)
    (complete : state.remaining = 0) :
    (NativeFieldVectorValues.project goldilocksModulus size 0 state).map (reshape ctx size same) =
      some (SingleOpeningRecoveredMatrix.random ctx state) := by
  simp only [NativeFieldVectorValues.project,complete,ite_true,Option.map_some,Nat.zero_add]
  congr 1
  funext lane row
  rw [reshape_apply]
  rfl
/-- Eligibility uses the original native geometry, not a supplied count. -/
theorem prepared_count (ctx : Context) (world : InputIndexedOracle.World) (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (OracleProgram.run ctx.prefix world).run.1 = .prepared work) :
    work.geometry.randomCount.val = count ctx := by
  rw [SingleOpeningRandomLaw.count prepared,(SingleOpeningRectangularData.dimensions ctx world work prepared).2.2]
  rfl
end
end FormalProof4FHE.HasteBoots.SingleOpeningFieldMatrix
