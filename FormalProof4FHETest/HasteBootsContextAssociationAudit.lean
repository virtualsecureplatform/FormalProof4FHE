module
import FormalProof4FHE.HasteBoots.GoldContextInput
import FormalProof4FHE.HasteBoots.GoldContextCollision
import FormalProof4FHE.HasteBoots.LookupContextHistory
import FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.Fields' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.Fields

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.codec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.codec

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.fields' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.fields

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.bytes

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.input_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.input_eq

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.fields_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.fields_injective

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextInput.bytes_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextInput.bytes_injective

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextCollision.context_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextCollision.context_run

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextCollision.observed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextCollision.observed

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextCollision.parameters_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextCollision.parameters_eq

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextCollision.parameters_eq_of_no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextCollision.parameters_eq_of_no_bad

/-- info: 'FormalProof4FHE.HasteBoots.GoldContextCollision.parameters_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.GoldContextCollision.parameters_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.LookupContextHistory.loop_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupContextHistory.loop_context

/-- info: 'FormalProof4FHE.HasteBoots.LookupContextHistory.program_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupContextHistory.program_context

/-- info: 'FormalProof4FHE.HasteBoots.LookupContextHistory.used_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupContextHistory.used_context

/-- info: 'FormalProof4FHE.HasteBoots.LookupContextHistory.receipt_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupContextHistory.receipt_context

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.Associated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.Associated

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.associated_no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.associated_no_bad

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.associated_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.associated_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.all_associated_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupSourceParameterAssociation.all_associated_or_bad
