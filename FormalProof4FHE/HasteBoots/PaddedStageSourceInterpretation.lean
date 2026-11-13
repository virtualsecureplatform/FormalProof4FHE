module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
public import FormalProof4FHE.HasteBoots.PaddedNTT
public import FormalProof4FHE.HasteBoots.PaddedLinear
public import FormalProof4FHE.HasteBoots.PaddedZeroCheck
public import FormalProof4FHE.HasteBoots.PaddedPublicZeroCheck
@[expose] public section

/-! Normalize the actual padded verifier source definitions to one fixed
physical decoder and native-address view. Descriptor association across calls
is public parameter association, not a supplied source-value equality. -/
namespace FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
noncomputable section
variable {F Input Digest Cfg Response Memory CommitMemory Factor Private Public Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [DecidableEq Digest]
  {heights : Cfg → ℕ} {b c r k n count : ℕ}

def nttParameters (s : PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory heights b c r k)
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ) (side : Bool) :
    RecordedPaddedSource.Parameters F Cfg heights b :=
  ⟨(s.code side).front,(s.code side).suffix,(s.code side).m,s.tag side,s.domain side,capacity side,radius side⟩

/-- Every NTT row source is a view of its own actual physical decoder. -/
theorem ntt_original (s : PaddedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory heights b c r k)
    (dummy : Digest) (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*b) (radius : Bool → ℕ)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side)) (side : Bool) :
    PaddedNTT.originalSources s dummy capacity radius owner side =
      RecordedPaddedSource.logical (nttParameters s capacity radius side) s.encoding dummy (r+c) (owner side) :=
  RecordedPaddedSource.padded_eq_logical (nttParameters s capacity radius side) s.encoding dummy
    (s.padding side) (s.dimensions side) (owner side)

def linearParameters (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory heights count b n)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ) (factor : Fin count) :
    RecordedPaddedSource.Parameters F Cfg heights b :=
  ⟨(s.code factor).front,(s.code factor).suffix,(s.code factor).m,s.tag factor,s.domain factor,capacity factor,radius factor⟩

/-- Linear reconstruction uses the same native-address convention. -/
theorem linear_original (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory heights count b n)
    (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin count → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) (factor : Fin count) :
    PaddedLinear.originalSources s dummy capacity radius owner factor =
      RecordedPaddedSource.logical (linearParameters s capacity radius factor) s.encoding dummy n (owner factor) :=
  RecordedPaddedSource.padded_eq_logical (linearParameters s capacity radius factor) s.encoding dummy
    (s.padding factor) (s.dimensions factor) (owner factor)

def zeroParameters (s : PaddedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Factor → ℕ) (factor : Factor) :
    RecordedPaddedSource.Parameters F Cfg heights b :=
  ⟨(s.code factor).front,(s.code factor).suffix,(s.code factor).m,s.tag factor,s.domain factor,capacity factor,radius factor⟩

/-- Private product factors use the same decoded physical matrix view. -/
theorem zero_original (s : PaddedZeroCheck.Scheme F Factor Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n)
    (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Factor → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) (factor : Factor) :
    PaddedZeroCheck.originalSources s dummy capacity radius owner factor =
      RecordedPaddedSource.logical (zeroParameters s capacity radius factor) s.encoding dummy (n+1) (owner factor) :=
  RecordedPaddedSource.padded_eq_logical (zeroParameters s capacity radius factor) s.encoding dummy
    (s.padding factor) (s.dimensions factor) (owner factor)

def publicZeroParameters (s : PaddedPublicZeroCheck.Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ) (factor : Private) :
    RecordedPaddedSource.Parameters F Cfg heights b :=
  ⟨(s.code factor).front,(s.code factor).suffix,(s.code factor).m,s.tag factor,s.domain factor,capacity factor,radius factor⟩

/-- Extraction's private factor uses the canonical source view; verifier public
factors remain the fixed public tables from the original execution. -/
theorem publicZero_original (s : PaddedPublicZeroCheck.Scheme F Private Public Term FirstMessage Message Input Digest Cfg Response Memory CommitMemory heights b n)
    (dummy : Digest) (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Private → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) (factor : Private) :
    PaddedPublicZeroCheck.originalSources s dummy capacity radius owner factor =
      RecordedPaddedSource.logical (publicZeroParameters s capacity radius factor) s.encoding dummy (n+1) (owner factor) :=
  RecordedPaddedSource.padded_eq_logical (publicZeroParameters s capacity radius factor) s.encoding dummy
    (s.padding factor) (s.dimensions factor) (owner factor)

end
end FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
