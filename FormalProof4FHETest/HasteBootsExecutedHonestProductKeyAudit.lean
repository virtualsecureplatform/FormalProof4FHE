module
import all FormalProof4FHE.HasteBoots.ExecutedHonestProductKey

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.withKeys' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.withKeys

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.parameters

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.setup

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.source_key_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestProductKey.source_key_eq_or_bad
