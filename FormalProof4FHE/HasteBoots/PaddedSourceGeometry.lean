module
public import FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
@[expose] public section

/-! Construct stage source layouts from public decoder descriptors. Physical
workers are supplied at the derived native types; logical callbacks and commit
work remain those of the raw scheme. No source-value equality is an input. -/
namespace FormalProof4FHE.HasteBoots.PaddedSourceGeometry
noncomputable section
variable {F Cfg Input Digest Response Memory CommitMemory Factor Term FirstMessage Message : Type}
  [Field F] {H : Cfg → ℕ} {b logical c r k n count : ℕ}

structure Geometry (F Cfg Index : Type) [Field F] (H : Cfg → ℕ) (b logical : ℕ) where
  parameters : Index → RecordedPaddedSource.Parameters F Cfg H b
  queries : Index → ℕ
  fits : ∀ index, logical ≤ (parameters index).front+(parameters index).suffix

def code {Index : Type} (g : Geometry F Cfg Index H b logical) (index : Index) : HeterogeneousSingleOpening.Layout :=
  ⟨(g.parameters index).front,(g.parameters index).suffix,(g.parameters index).degree,g.queries index⟩

def nttCode (g : Geometry F Cfg Bool H b logical) (side : Bool) : PaddedNTT.Code :=
  ⟨(g.parameters side).front,(g.parameters side).suffix,(g.parameters side).degree,g.queries side⟩

def padding {Index : Type} (g : Geometry F Cfg Index H b logical) (index : Index) : ℕ :=
  (g.parameters index).front+(g.parameters index).suffix-logical

theorem dimensions {Index : Type} (g : Geometry F Cfg Index H b logical) (index : Index) :
    padding g index+logical = (g.parameters index).front+(g.parameters index).suffix :=
  Nat.sub_add_cancel (g.fits index)

/-- Fix both NTT source descriptors and use physical workers typed by them. -/
def ntt (raw : PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory H b c r k)
    (g : Geometry F Cfg Bool H b (r+c))
    (build : ((Bool → Digest) × CommitMemory) → AuthenticatedNTT.Packet F Memory c b r k → (side : Bool) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b (g.parameters side).front (g.parameters side).suffix k
        (g.parameters side).degree (g.queries side) (H (g.parameters side).tag)) :=
  {raw with
    tag := fun side => (g.parameters side).tag
    code := nttCode g
    padding := padding g
    dimensions := dimensions g
    domain := fun side => (g.parameters side).domain
    build := build}

/-- Fix reconstruction descriptors while retaining its logical protocol work. -/
def linear (raw : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H count b n)
    (g : Geometry F Cfg (Fin count) H b n)
    (build : ((Fin count → Digest) × CommitMemory) → PackedLinearOracle.Packet F (Fin count) Memory b n → (factor : Fin count) →
      SingletonOpening.Protocol F Input Digest Cfg Response Memory b (g.parameters factor).front (g.parameters factor).suffix
        (g.parameters factor).degree (g.queries factor) (H (g.parameters factor).tag)) :=
  {raw with
    tag := fun factor => (g.parameters factor).tag
    code := code g
    padding := padding g
    dimensions := dimensions g
    domain := fun factor => (g.parameters factor).domain
    build := build}

/-- Fix private product descriptors and retain all logical callbacks. -/
def zero (raw : PaddedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory H b n)
    (g : Geometry F Cfg Factor H b (n+1))
    (build : ((Factor → Digest) × CommitMemory) → PreparedZeroTerminal.Packet F Factor Memory b n → (factor : Factor) →
      HeterogeneousSingleOpening.Protocol F Input Digest Cfg Response Memory b H
        (fun factor => (g.parameters factor).tag) (code g) factor) :=
  {raw with
    tag := fun factor => (g.parameters factor).tag
    code := code g
    padding := padding g
    dimensions := dimensions g
    domain := fun factor => (g.parameters factor).domain
    build := build}

/-- The constructed NTT exposes exactly its public source descriptor. -/
theorem ntt_parameters
    (raw : PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory H b c r k)
    (g : Geometry F Cfg Bool H b (r+c))
    (build : ((Bool → Digest) × CommitMemory) → AuthenticatedNTT.Packet F Memory c b r k → (side : Bool) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b (g.parameters side).front (g.parameters side).suffix k
        (g.parameters side).degree (g.queries side) (H (g.parameters side).tag)) (side : Bool) :
    PaddedStageSourceInterpretation.nttParameters (ntt raw g build)
      (fun side => (g.parameters side).capacity) (fun side => (g.parameters side).radius) side = g.parameters side := rfl

theorem linear_parameters
    (raw : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H count b n)
    (g : Geometry F Cfg (Fin count) H b n)
    (build : ((Fin count → Digest) × CommitMemory) → PackedLinearOracle.Packet F (Fin count) Memory b n → (factor : Fin count) →
      SingletonOpening.Protocol F Input Digest Cfg Response Memory b (g.parameters factor).front (g.parameters factor).suffix
        (g.parameters factor).degree (g.queries factor) (H (g.parameters factor).tag)) (factor : Fin count) :
    PaddedStageSourceInterpretation.linearParameters (linear raw g build)
      (fun factor => (g.parameters factor).capacity) (fun factor => (g.parameters factor).radius) factor = g.parameters factor := rfl

theorem zero_parameters
    (raw : PaddedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory H b n)
    (g : Geometry F Cfg Factor H b (n+1))
    (build : ((Factor → Digest) × CommitMemory) → PreparedZeroTerminal.Packet F Factor Memory b n → (factor : Factor) →
      HeterogeneousSingleOpening.Protocol F Input Digest Cfg Response Memory b H
        (fun factor => (g.parameters factor).tag) (code g) factor) (factor : Factor) :
    PaddedStageSourceInterpretation.zeroParameters (zero raw g build)
      (fun factor => (g.parameters factor).capacity) (fun factor => (g.parameters factor).radius) factor = g.parameters factor := rfl

/-- Installing public geometry preserves the raw NTT commitment computation. -/
theorem ntt_commit
    (raw : PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory H b c r k)
    (g : Geometry F Cfg Bool H b (r+c))
    (build : ((Bool → Digest) × CommitMemory) → AuthenticatedNTT.Packet F Memory c b r k → (side : Bool) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b (g.parameters side).front (g.parameters side).suffix k
        (g.parameters side).degree (g.queries side) (H (g.parameters side).tag)) :
    (ntt raw g build).commit = raw.commit := rfl

theorem linear_commit
    (raw : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H count b n)
    (g : Geometry F Cfg (Fin count) H b n)
    (build : ((Fin count → Digest) × CommitMemory) → PackedLinearOracle.Packet F (Fin count) Memory b n → (factor : Fin count) →
      SingletonOpening.Protocol F Input Digest Cfg Response Memory b (g.parameters factor).front (g.parameters factor).suffix
        (g.parameters factor).degree (g.queries factor) (H (g.parameters factor).tag)) :
    (linear raw g build).commit = raw.commit := rfl

theorem zero_commit
    (raw : PaddedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory H b n)
    (g : Geometry F Cfg Factor H b (n+1))
    (build : ((Factor → Digest) × CommitMemory) → PreparedZeroTerminal.Packet F Factor Memory b n → (factor : Factor) →
      HeterogeneousSingleOpening.Protocol F Input Digest Cfg Response Memory b H
        (fun factor => (g.parameters factor).tag) (code g) factor) :
    (zero raw g build).commit = raw.commit := rfl

end
end FormalProof4FHE.HasteBoots.PaddedSourceGeometry
