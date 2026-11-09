module
import all FormalProof4FHE.HasteBoots.NativeRecordHeapBounds

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.count' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.count

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_count

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_blocks

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.trans' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.no_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.no_growth

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.unchanged

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.single

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.blocks_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.blocks_sublist

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.generation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.generation

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.shadow_sublist' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.shadow_sublist

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.single_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.single_block

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.release_readBlocks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.release_readBlocks

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_range_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_range_frame

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.shadow_lookup_filter_owner' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.shadow_lookup_filter_owner

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.shadow_uniform_filter_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.shadow_uniform_filter_owner

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_load_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.deallocate_load_frame

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.refl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.refl

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.free' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapRelease.Releases.free

/-- info: 'FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.released' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHeapLoss.Loss.released

