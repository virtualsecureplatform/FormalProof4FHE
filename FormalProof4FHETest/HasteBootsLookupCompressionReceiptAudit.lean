module
import all FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder
import all FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch
import all FormalProof4FHE.HasteBoots.LookupCompressionReceipt
import all FormalProof4FHE.HasteBoots.QuotedReceiptCoverage
import all FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation
import all FormalProof4FHE.HasteBoots.LookupOffsetKernel
import all FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery
import all FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.Before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.Before

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.append

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.Traced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.Traced

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.initial

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptOrder.execute

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.Certificates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.Certificates

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.after_sample' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.after_sample

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.tick

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.execute

/-- info: 'FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupDrawReceiptBatch.initialized

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.latest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.latest

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.member

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.labels_distinct' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.labels_distinct

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.tail_filter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.tail_filter

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.at_offset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.at_offset

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.original

/-- info: 'FormalProof4FHE.HasteBoots.LookupCompressionReceipt.last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupCompressionReceipt.last

/-- info: 'FormalProof4FHE.HasteBoots.QuotedReceiptCoverage.named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.QuotedReceiptCoverage.named

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.Candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.Candidate

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.compression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.compression

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.y_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.y_fixed

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.test_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetCompressionFixation.test_fixed

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetKernel.complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetKernel.complexity

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetKernel.Event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetKernel.Event

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetKernel.event_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetKernel.event_fixed

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetKernel.complexity_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetKernel.complexity_fixed

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetKernel.conditional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetKernel.conditional_bound

/-- info: 'FormalProof4FHE.HasteBoots.LookupOffsetKernel.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.LookupOffsetKernel.bound

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.receipts

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.candidate

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.recover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.recover

/-- info: 'FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery.bound

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.prior' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.prior

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.current' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.current

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.rejected

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.accepted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.accepted

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.valid

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.latest_after_rejections' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.latest_after_rejections

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.no_compression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.no_compression

/-- info: '_private.FormalProof4FHETest.HasteBootsLookupCompressionReceiptSmoke.0.HasteBootsLookupCompressionReceiptSmoke.receipt_key_not_compression' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasteBootsLookupCompressionReceiptSmoke.receipt_key_not_compression
