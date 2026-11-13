module
import all FormalProof4FHE.HasteBoots.HonestMerkleTranscript

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.program' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.program

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.tree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.tree

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.queries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.queries

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.handler' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.handler

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.run

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.answered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.answered

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.query_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.query_count

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.leaf_query' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.leaf_query

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.extracted_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.extracted_tree

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.payload_recovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.payload_recovered

/-- info: 'FormalProof4FHE.HasteBoots.HonestMerkleTranscript.word_recovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HonestMerkleTranscript.word_recovered
