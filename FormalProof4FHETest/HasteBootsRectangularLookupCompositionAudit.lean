module
import all FormalProof4FHE.HasteBoots.RectangularStagedException
import all FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening
import all FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS
import all FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
import all FormalProof4FHE.HasteBoots.RectangularStagedLookupSoundness
import all FormalProof4FHE.HasteBoots.RectangularLookupConditionalSoundness
import all FormalProof4FHE.HasteBoots.ConstructedGoldLookupConditional

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedException.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedException.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.CommitMemory' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.CommitMemory

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.build

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.words

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.wrong_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.wrong_iff

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.soundness_from_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupGroupedOpening.soundness_from_empty

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.Emission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.Emission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.Selection' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.Selection

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.Result' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.Result

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.packets' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.packets

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.enabled' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.enabled

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.start' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.start

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.program

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.support_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.support_accepts

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.reduce_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.reduce_acceptance

/-- info: 'FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularSharedLookupPCS.arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Pair' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Pair

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.pairValues' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.pairValues

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.SourceEmission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.SourceEmission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.HelperEmission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.HelperEmission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Emission' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Emission

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Parameters

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Config' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.Config

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.verifier

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.continuation

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.AllPass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.AllPass

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.badIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.badIndex

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.ArithmeticEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.ArithmeticEvent

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.pcsError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup.pcsError

/-- info: 'FormalProof4FHE.HasteBoots.RectangularStagedLookupSoundness.bad_prefix_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularStagedLookupSoundness.bad_prefix_or_bad_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupConditionalSoundness.bad_prefix_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupConditionalSoundness.bad_prefix_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldLookupConditional.bad_prefix_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldLookupConditional.bad_prefix_safe_bound
