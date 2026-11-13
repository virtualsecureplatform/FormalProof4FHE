module
import all FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier
import all FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
import all FormalProof4FHE.HasteBoots.RectangularRecordedOpening
import all FormalProof4FHE.HasteBoots.RectangularStagedOpening
import all FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup
import all FormalProof4FHE.HasteBoots.RectangularStagedSquareCompatibility

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier.checks_wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier.checks_wrong_implies_arithmetic_or_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier.step_wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier.step_wrong_implies_arithmetic_or_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Layout' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Layout

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.error

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Protocol' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Protocol

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Data

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.requests' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.requests

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.snapshots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.snapshots

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.snapshots_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.snapshots_recorded

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.protocol' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.protocol

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.continuation

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.Wrong

/-- info: 'FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRecordedOpening.Snapshots' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRecordedOpening.Snapshots

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRecordedOpening.Arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRecordedOpening.Arithmetic

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRecordedOpening.Wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRecordedOpening.Wrong

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRecordedOpening.reduce_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRecordedOpening.reduce_wrong

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRecordedOpening.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRecordedOpening.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.SourceEmission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.SourceEmission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.HelperEmission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.HelperEmission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.CommitMemory' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.CommitMemory

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.emission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.emission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.factors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.factors

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.factors_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.factors_complete

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.sourceRequests' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.sourceRequests

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.helperRequests' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.helperRequests

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.snapshots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.snapshots

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.snapshots_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.snapshots_roots

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.snapshots_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.snapshots_recorded

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.continuation

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedOpening.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.layout

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.degree_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.degree_positive

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.enough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.enough

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.Emission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.Emission

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.Packet' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.Packet

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.build

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSquareCompatibility.continuation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSquareCompatibility.continuation_eq
