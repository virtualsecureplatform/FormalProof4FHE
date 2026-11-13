module
import all FormalProof4FHE.HasteBoots.RectangularRequestLookup
import all FormalProof4FHE.HasteBoots.RectangularPrivateSharedLookup
import all FormalProof4FHE.HasteBoots.RectangularPrivateLookupConditional
import all FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources
import all FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources
import all FormalProof4FHE.HasteBoots.RectangularLookupOwnerConditional
import all FormalProof4FHE.HasteBoots.RectangularOwnedRequestConditional
import all FormalProof4FHE.HasteBoots.RectangularOwnedLookupConditional
import all FormalProof4FHE.HasteBoots.RectangularOwnedPrivateSharedLookup
import all FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.request

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.request_job' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.request_job

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.Parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.Parameters

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.toParameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.toParameters

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.columns

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.tuples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.tuples

/-- info: 'FormalProof4FHE.HasteBoots.RectangularRequestLookup.allPass_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularRequestLookup.allPass_iff

/-- info: 'FormalProof4FHE.HasteBoots.RectangularPrivateSharedLookup.allPass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularPrivateSharedLookup.allPass_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularPrivateSharedLookup.false_acceptance_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularPrivateSharedLookup.false_acceptance_or_bad_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularPrivateLookupConditional.false_acceptance_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularPrivateLookupConditional.false_acceptance_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.Owners' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.Owners

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.FirstPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.FirstPrefix

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.SecondPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.SecondPrefix

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.Outcome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.Outcome

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.columns

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.freshColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.freshColumns

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.columns_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources.columns_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.Config' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.Config

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.tuples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.tuples

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.OriginalFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.OriginalFalse

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.fresh_false_implies_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.fresh_false_implies_original

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.original_false_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources.original_false_reduction

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupOwnerConditional.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupOwnerConditional.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.RectangularLookupOwnerConditional.columns_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularLookupOwnerConditional.columns_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedRequestConditional.original_false_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedRequestConditional.original_false_reduction

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedLookupConditional.false_acceptance_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedLookupConditional.false_acceptance_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.RectangularOwnedPrivateSharedLookup.false_acceptance_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RectangularOwnedPrivateSharedLookup.false_acceptance_or_bad_bound

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional.radius_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional.radius_large

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional.radius_large_of_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional.radius_large_of_distance

/-- info: 'FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional.false_acceptance_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional.false_acceptance_safe_bound
