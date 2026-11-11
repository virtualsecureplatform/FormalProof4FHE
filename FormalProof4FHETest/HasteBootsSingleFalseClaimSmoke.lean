module
import all FormalProof4FHE.HasteBoots.SingleOpeningConcreteExposureCoverage
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke
import all Init.Data.String.Defs

namespace FormalProof4FHE.HasteBoots.SingleFalseClaimSmoke
noncomputable section
open OracleProgram (run)

namespace Matrix
abbrev F := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def domain : Bool ↪ F := ⟨fun bit => if bit then 1 else 0,by
  intro first second same
  cases first <;> cases second <;> simp_all⟩

def table : Unit → Fin 1 → Fin 2 → F := fun _ _ _ => 0
def left (_ : Unit) : Matrix (Fin 2) (Fin 2) F := 1
def right (_ : Fin 1) : Matrix (Fin 2) (Fin 2) F := 1
def messages (lane : Fin 2) (_ : Fin 1) : F := if lane = 0 then 0 else 1

def word (position : Bool) (row : Unit × Fin 2) : Fin 1 → F :=
  BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 1) (fun index => table row.1 index row.2)) position

theorem extracted : RectangularMatrixOpeningKernel.extract domain (by decide : 1 ≤ 1*1) 0 word = table :=
  RectangularMatrixOpeningKernel.extract_encoded domain (by decide) (by decide) table

example : RectangularMatrixResponse.finishMessage right messages ≠ matrixEvaluation left right table := by decide +kernel

/-- A false structured finishing supplies one lane witness, without a lane sum. -/
example : ∃ lane : Fin 2, Code.minDist (BlockCode.code domain 1 1 : Set (Bool → Fin 1 → F)) ≤
    hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights left lane) word)
      (BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 1) (messages lane))) := by
  have near : ∃ close, CommonSource.RowsIn (BlockCode.code domain 1 1) close ∧ hammingDist word close ≤ 0 :=
    ⟨word,(fun _ => BlockEncoder.encode_mem_code domain _),by simp⟩
  have falseClaim : RectangularMatrixResponse.finishMessage right messages ≠
      matrixEvaluation left right (RectangularMatrixOpeningKernel.extract domain (by decide : 1 ≤ 1*1) 0 word) := by
    rw [extracted]
    decide +kernel
  simpa only [Nat.sub_zero] using RectangularMatrixDisagreement.near_witness domain (by decide) (by decide) 0 word left right messages near falseClaim

/-- The honest lane agrees; the wrong lane disagrees on both columns. -/
example : hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights left (0 : Fin 2)) word)
      (BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 1) (messages 0))) = 0 ∧
    hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights left (1 : Fin 2)) word)
      (BlockEncoder.encode domain (RowLayout.padded (m := 1) (b := 1) (messages 1))) = 2 := by decide +kernel
end Matrix

namespace Native
open SingleSelectedSmoke (ctx world work prepared)

def choose : NativeGoldPcsProgram.Scheduler Unit := fun work workers _ =>
  .pure ((List.finRange work.jobs.length).find? (fun index => !HashWorkerPool.done (workers index)),())

def resultTag (outcome : NativeGoldPcsProgram.Outcome Unit) : ℕ :=
  match outcome with
  | .completed _ completion => match completion.status with
    | .accepted _ => 1
    | .claim .claim => 2
    | _ => 3
  | _ => 0

/-- Both actual native authentication workers and native finishing accept. -/
example : resultTag (run (NativeGoldPcsProgram.program ctx choose 20 ()) world).run.1 = 1 := by decide +kernel

/-- The same original zero response cannot pass a nonzero original claim. -/
example : resultTag (run (NativeGoldPcsProgram.program
    {ctx with claimed := ⟨[1,0,0],by decide⟩} choose 20 ()) world).run.1 = 2 := by decide +kernel
end Native

end
end FormalProof4FHE.HasteBoots.SingleFalseClaimSmoke
