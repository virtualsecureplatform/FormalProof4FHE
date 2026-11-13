module
public import FormalProof4FHE.HasteBoots.ConstructedGoldLookupGeometry
@[expose] public section

/-! Concrete Gold lookup opening protocols use the constructed native domain,
geometry and width policy together with the actual terminal packet. Behavioral
callbacks supply only prover work, columns and scheduling; their query, value,
encoding, domain and root fields are replaced by the trusted binding. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldLookupProtocol
open ClassicalGoldRoleBundle (Bundle Stage roleIndex parameters)
open NativeFields (Goldilocks)
open ConstructedGoldSourceDescriptor (Configuration heights)
open PaddedMixedWidthLookupOpeningFamily (Root packedWidth)
noncomputable section

structure Context (row count repetitions : ℕ) where
  bundle : Bundle
  sources : Fin count → Stage
  helpers : Fin repetitions → Stage
  sourceRoles : ∀ source, roleIndex (sources source) = 0 ∨ roleIndex (sources source) = 2
  helperRoles : ∀ helper, roleIndex (helpers helper) = 1 ∨ roleIndex (helpers helper) = 3
  sourceFits : ∀ source, row ≤ (parameters bundle (sources source)).numVariables.val
  helperFits : ∀ helper, 2+row ≤ (parameters bundle (helpers helper)).numVariables.val

variable {row count repetitions : ℕ}

def geometry (ctx : Context row count repetitions) :=
  ConstructedGoldLookupGeometry.geometry ctx.bundle ctx.sources ctx.helpers ctx.sourceFits ctx.helperFits

def tag (ctx : Context row count repetitions) := ConstructedGoldLookupGeometry.tag ctx.bundle ctx.sources ctx.helpers

def domain (ctx : Context row count repetitions) := ConstructedGoldLookupGeometry.domain ctx.bundle ctx.sources ctx.helpers

theorem capacity (ctx : Context row count repetitions) (root : Root count repetitions) :
    2^((geometry ctx).suffix root) ≤ ((geometry ctx).m root) * 4 :=
  ConstructedGoldLookupGeometry.geometry_capacity ctx.bundle ctx.sources ctx.helpers ctx.sourceFits ctx.helperFits root

theorem native_widths (ctx : Context row count repetitions) (root : Root count repetitions) :
    (tag ctx root).width.val = packedWidth 4 3 root ∧ (tag ctx root).code.blockWidth.val = 4 :=
  ConstructedGoldLookupGeometry.native_widths ctx.bundle ctx.sources ctx.helpers ctx.sourceRoles ctx.helperRoles root

abbrev Behavior (Input Digest Response Memory : Type) (ctx : Context row count repetitions) (root : Root count repetitions) :=
  RectangularBatchVerifier.Protocol Goldilocks Input Digest Configuration Response Memory
    (packedWidth 4 3 root) 4 ((geometry ctx).front root) ((geometry ctx).suffix root)
    (PaddedMixedWidthLookupOpeningFamily.layout (geometry ctx) root).claims
    ((geometry ctx).m root) ((geometry ctx).queries root) (heights (tag ctx root))

variable {K Input Digest Response Memory : Type} [Field K] [Algebra Goldilocks K]

def protocol (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (packet : PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions)
    (encoding : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Root count repetitions → Digest)
    (root : Root count repetitions) (behavior : Behavior Input Digest Response Memory ctx root) :
    Behavior Input Digest Response Memory ctx root :=
  { RectangularPaddedLookupOpeningFamily.bind (d := 3) (padding := 1) (helperPadding := 0)
      (g := geometry ctx) (heights := heights) (tag := tag ctx) (symbolWidth := fun _ => 4) basis (by decide +kernel) packet root behavior with
    encoding := encoding, domain := domain ctx root, root := roots root }

theorem protocol_domain (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (packet : PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions)
    (encoding : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Root count repetitions → Digest)
    (root : Root count repetitions) (behavior : Behavior Input Digest Response Memory ctx root) :
    (protocol ctx basis packet encoding roots root behavior).domain = domain ctx root := rfl

theorem protocol_query (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (packet : PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions)
    (encoding : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Root count repetitions → Digest)
    (root : Root count repetitions) (behavior : Behavior Input Digest Response Memory ctx root) :
    (protocol ctx basis packet encoding roots root behavior).query =
      PaddedMixedWidthLookupOpeningFamily.queries (padding := 1) (helperPadding := 0) basis (by decide +kernel)
        (geometry ctx) packet root := rfl

theorem protocol_values (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (packet : PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions)
    (encoding : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Root count repetitions → Digest)
    (root : Root count repetitions) (behavior : Behavior Input Digest Response Memory ctx root) :
    (protocol ctx basis packet encoding roots root behavior).values =
      PaddedMixedWidthLookupOpeningFamily.values (padding := 1) (helperPadding := 0) basis (geometry ctx) packet root := rfl

theorem protocol_binding (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (packet : PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions)
    (encoding : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Root count repetitions → Digest)
    (root : Root count repetitions) (behavior : Behavior Input Digest Response Memory ctx root) :
    (protocol ctx basis packet encoding roots root behavior).encoding = encoding ∧
      (protocol ctx basis packet encoding roots root behavior).root = roots root := ⟨rfl,rfl⟩

/-- The rectangular terminal's wrong-value event is literally the one used by
soundness of the actual bound worker protocol, with constructor-derived capacity. -/
theorem wrongValue_iff (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (packet : PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions)
    (encoding : MerkleOracle.Encoding Input Digest (List Goldilocks)) (roots : Root count repetitions → Digest)
    (radius : Root count repetitions → ℕ)
    (words : ∀ root : Root count repetitions, Fin (2^heights (tag ctx root)) →
      (Fin (2^(geometry ctx).front root) × Fin (packedWidth 4 3 root)) → Fin 4 → Goldilocks)
    (root : Root count repetitions) (claim : Fin (PaddedMixedWidthLookupOpeningFamily.layout (geometry ctx) root).claims)
    (behavior : Behavior Input Digest Response Memory ctx root) :
    RectangularPaddedLookupOpeningFamily.WrongValue (d := 3) (padding := 1) (helperPadding := 0)
      (g := geometry ctx) (heights := heights) (tag := tag ctx) basis (by decide +kernel)
      packet (domain ctx) (capacity ctx) radius words root claim ↔
    let p := protocol ctx basis packet encoding roots root behavior
    p.values claim ≠ matrixEvaluation
      (NativeBatchChecks.left p.query claim) (NativeBatchChecks.right p.query claim)
      (RectangularMatrixOpeningKernel.extract p.domain (capacity ctx root) (radius root) (words root)) := Iff.rfl

end
end FormalProof4FHE.HasteBoots.ConstructedGoldLookupProtocol
