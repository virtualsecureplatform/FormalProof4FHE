module

public import FormalProof4FHE.HasteBoots.NativeFields
public import FormalProof4FHE.HasteBoots.SymbolLift
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

/-!
# Constructed finite alphabets for PCS row-span analysis

The AHIV22 analysis needs a degree-b extension of the base field, with one
basis element per symbol lane. This is a proof device; the protocol samples
base-field matrices and never calls its auxiliary sampler. GaloisField
constructs this alphabet and its basis, independently of the lookup extension
and without an extension-existence or basis certificate supplied by the prover.
-/

namespace FormalProof4FHE.HasteBoots.PCSAnalysisField

noncomputable section

variable (p b : ℕ) [Fact p.Prime]

abbrev Alphabet := GaloisField p b

instance : Fintype (Alphabet p b) := Fintype.ofFinite _
instance : DecidableEq (Alphabet p b) := Classical.decEq _
instance : SampleableType (Alphabet p b) := SampleableType.ofFintype _

variable [NeZero b]

theorem dimension : Module.finrank (ZMod p) (Alphabet p b) = b :=
  GaloisField.finrank p (NeZero.ne b)

/-- Fixed before all protocol challenges; basis choice occurs only in proofs. -/
def basis : Module.Basis (Fin b) (ZMod p) (Alphabet p b) :=
  Module.finBasisOfFinrankEq (ZMod p) (Alphabet p b) (dimension p b)

theorem cardinality : Fintype.card (Alphabet p b) = p ^ b := by
  rw [SymbolLift.cardinality (basis p b), ZMod.card]

abbrev GoldilocksAlphabet := Alphabet NativeFields.goldilocksModulus 4
abbrev BabyBearAlphabet := Alphabet NativeFields.babyBearModulus 8

def goldilocksBasis : Module.Basis (Fin 4) NativeFields.Goldilocks GoldilocksAlphabet :=
  basis NativeFields.goldilocksModulus 4

def babyBearBasis : Module.Basis (Fin 8) NativeFields.BabyBear BabyBearAlphabet :=
  basis NativeFields.babyBearModulus 8

theorem goldilocks_card : Fintype.card GoldilocksAlphabet = NativeFields.goldilocksModulus ^ 4 :=
  cardinality _ _

theorem babyBear_card : Fintype.card BabyBearAlphabet = NativeFields.babyBearModulus ^ 8 :=
  cardinality _ _

end

end FormalProof4FHE.HasteBoots.PCSAnalysisField
