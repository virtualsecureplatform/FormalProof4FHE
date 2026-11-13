module
import all FormalProof4FHE.HasteBoots.ExecutedHonestCommitment

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.program' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.program

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.commit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.commit

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.tree_of_answers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.tree_of_answers

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.hash_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.hash_log

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.transcript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.transcript

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.recorded

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.retained

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.realized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.realized

/-- info: 'FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.realized_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutedHonestCommitment.realized_recorded
