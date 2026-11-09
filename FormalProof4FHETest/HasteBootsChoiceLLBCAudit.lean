module
import all FormalProof4FHE.HasteBoots.NativeRecordLLBC
import all FormalProof4FHE.HasteBoots.NativeVariantValues

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordValues.Ty.choice' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordValues.Ty.choice

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordValues.Value.choice' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordValues.Value.choice

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordValues.Step.active' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordValues.Step.active

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordValues.sideAt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordValues.sideAt

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Input.choice' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Input.choice

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Rvalue.choice' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Rvalue.choice

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Rvalue.aggregate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Rvalue.aggregate

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.Body.matchChoice' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.Body.matchChoice

/-- info: 'FormalProof4FHE.HasteBoots.NativeRecordLLBC.selectChoice' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeRecordLLBC.selectChoice

/-- info: 'FormalProof4FHE.HasteBoots.NativeVariantValues.binaryType' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeVariantValues.binaryType

/-- info: 'FormalProof4FHE.HasteBoots.NativeVariantValues.binaryValue' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeVariantValues.binaryValue

/-- info: 'FormalProof4FHE.HasteBoots.NativeVariantValues.binary_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeVariantValues.binary_fits

/-- info: 'FormalProof4FHE.HasteBoots.NativeVariantValues.binary_get' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeVariantValues.binary_get

/-- info: 'FormalProof4FHE.HasteBoots.NativeVariantValues.binary_replace' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeVariantValues.binary_replace

/-- info: 'FormalProof4FHE.HasteBoots.NativeVariantValues.binary_side' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeVariantValues.binary_side

