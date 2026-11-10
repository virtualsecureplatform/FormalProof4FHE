module
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldMatrix
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnFamily
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldExposure
public import FormalProof4FHE.HasteBoots.RectangularBaseProximity
@[expose] public section

/-! First-field proximity uses a source selected from the original past,
not later accepted work. The native ordered coefficient vector supplies the
whole random matrix; all native candidate budgets share one proximity loss. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFieldProximity
open NativeGoldPcsExecution (Context)
open SingleOpeningRectangularData (Row)
open SingleOpeningFieldInputView (View)
open NativeFields (Goldilocks)
open NativeGoldBlockCode (logSize)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open NativeIndexExposureRisk (Packet)
open InputIndexedOracle (World law)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
open scoped Classical
noncomputable section

def word (dummy : Digest) (ctx : Context) (history : List Observation) (field : View) :=
  SingleOpeningSelectedWord.word dummy field.data.context field.data.root ctx
    (SingleOpeningFirstFieldSource.selectedLog dummy history field)

def Far (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (source : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks) (radius : ℕ) : Prop :=
  ¬∃ close, CommonSource.RowsIn (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive)
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) close ∧ hammingDist source close ≤ radius

def matrixBad (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (source : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (radius : ℕ) (matrix : Fin ctx.parameters.width.val → Row ctx → Goldilocks) : Prop :=
  Far ctx primitive source radius ∧ ∀ lane,
    Code.distFromCode (StructuredOpening.combine (matrix lane) source)
      (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) ≤ radius

def bad (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (history : List Observation) (field : View) (vector : Fin field.count.val → Goldilocks) : Prop :=
  if same : field.count.val = SingleOpeningFieldMatrix.count ctx then
    matrixBad ctx primitive (word dummy ctx history field) radius (SingleOpeningFieldMatrix.reshape ctx field.count.val same vector)
  else False

def loss (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) : ENNReal :=
  ((Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
    Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) : ENNReal) / Fintype.card Goldilocks)^ctx.parameters.width.val

def score (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (history : List Observation) (field : View) : ENNReal :=
  if field.count.val = SingleOpeningFieldMatrix.count ctx ∧ Far ctx primitive (word dummy ctx history field) radius then loss ctx primitive else 0

theorem uniform_bound (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (history : List Observation) (field : View)
    (large : radius < Fintype.card Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks))) :
    Pr{let vector ← $ᵗ (Fin field.count.val → Goldilocks)}[bad dummy ctx primitive radius history field vector] ≤
      score dummy ctx primitive radius history field := by
  classical
  by_cases same : field.count.val = SingleOpeningFieldMatrix.count ctx
  · by_cases far : Far ctx primitive (word dummy ctx history field) radius
    · simp only [score,same,far,and_self,ite_true]
      let source := word dummy ctx history field
      let : SampleableType (Submodule.span Goldilocks (Set.range (RectangularBaseProximity.stack source))) := SampleableType.ofFintype _
      let : SampleableType (ModuleCodeProximity.toSpan (F := Goldilocks) (RectangularBaseProximity.stack source)).toAddMonoidHom.ker := SampleableType.ofFintype _
      calc
        _ = Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[matrixBad ctx primitive source radius matrix] := by
          have equal := prEvent_congr ($ᵗ (Fin field.count.val → Goldilocks))
            (bad dummy ctx primitive radius history field)
            (fun vector => matrixBad ctx primitive source radius (SingleOpeningFieldMatrix.reshape ctx field.count.val same vector))
            (fun vector => by simp only [bad,same,dite_true]; rfl)
          exact equal.trans (SingleOpeningFieldMatrix.uniform_reshape ctx field.count.val same _)
        _ ≤ Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → Row ctx → Goldilocks)}[∀ lane,
            Code.distFromCode (StructuredOpening.combine (matrix lane) source)
              (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
                Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) ≤ radius] :=
          prEvent_mono _ _ _ (fun _ member => member.2)
        _ ≤ _ := RectangularBaseProximity.matrix_bound _ _ _ _ source large small far
    · have zero : Pr{let vector ← $ᵗ (Fin field.count.val → Goldilocks)}[bad dummy ctx primitive radius history field vector] = 0 := by
        apply (SampleableType.prEvent_uniformSample_eq_zero_iff _).mpr
        intro vector
        simp [bad,same,matrixBad,far]
      rw [zero]
      exact zero_le
  · have zero : Pr{let vector ← $ᵗ (Fin field.count.val → Goldilocks)}[bad dummy ctx primitive radius history field vector] = 0 := by
      apply (SampleableType.prEvent_uniformSample_eq_zero_iff _).mpr
      intro vector
      simp [bad,same]
    rw [zero]
    exact zero_le
def event {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (profile : Digest) (step : S → OracleMachine.Command S A) (packet : Packet S A) (world : World) : Prop :=
  SingleOpeningFieldExposure.event profile step (fun old field => bad dummy ctx primitive radius old.2 field) packet world

def risk {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (step : S → OracleMachine.Command S A) (packet : Packet S A) : ENNReal :=
  match SingleOpeningFieldExposure.select step packet with
  | none => 0
  | some field => score dummy ctx primitive radius packet.2 field

theorem risk_bound {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (large : radius < Fintype.card Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks))) :
    SingleOpeningFieldExposure.risk step (fun old field => bad dummy ctx primitive radius old.2 field) packet ≤
      risk dummy ctx primitive radius step packet := by
  cases selected : SingleOpeningFieldExposure.select step packet with
  | none => simp only [SingleOpeningFieldExposure.risk,risk,selected,le_refl]
  | some field =>
    simp only [SingleOpeningFieldExposure.risk,risk,selected]
    exact uniform_bound dummy ctx primitive radius packet.2 field large small

theorem conditional_bound {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (profile : Digest) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (large : radius < Fintype.card Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks))) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event dummy ctx primitive radius profile step (past other).run other} ≤
        risk dummy ctx primitive radius step (past world).run :=
  (SingleOpeningFieldExposure.conditional_event_le profile step
    (fun old field => bad dummy ctx primitive radius old.2 field) replay world).trans
      (risk_bound dummy ctx primitive radius step (past world).run large small)

theorem event_measurable {S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (profile : Digest) (step : S → OracleMachine.Command S A)
    {past : World → Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) :
    MeasurableSet {world | event dummy ctx primitive radius profile step (past world).run world} :=
  SingleOpeningFieldExposure.event_measurable profile step (fun old field => bad dummy ctx primitive radius old.2 field) replay

def totalCharge {P S A : Type} (past : World → Execution P) (initial : P → S)
    (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (step : S → OracleMachine.Command S A) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk dummy ctx primitive radius step (CausalExposureLifetime.history past initial step fuel world).run

theorem lifetime_le {P S A : Type} {past : World → Execution P} (replay : ObservationReplay.Replayable past)
    (initial : P → S) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (profile : Digest) (step : S → OracleMachine.Command S A) (inherited : Set World)
    (large : radius < Fintype.card Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (SingleOpeningConcreteColumnFamily.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks))) :
    law (inherited ∪ {world | ∃ fuel, event dummy ctx primitive radius profile step
      (CausalExposureLifetime.history past initial step fuel world).run world}) ≤
        law inherited + ∫⁻ world, totalCharge past initial dummy ctx primitive radius step world ∂law := by
  apply (SingleOpeningFieldExposure.lifetime_le replay initial profile step
    (fun old field => bad dummy ctx primitive radius old.2 field) inherited).trans
  apply add_le_add le_rfl
  apply lintegral_mono
  intro world
  exact ENNReal.tsum_le_tsum (fun fuel => risk_bound dummy ctx primitive radius step _ large small)

end
end FormalProof4FHE.HasteBoots.SingleOpeningFieldProximity
