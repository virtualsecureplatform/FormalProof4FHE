module
public import FormalProof4FHE.HasteBoots.LookupIdentityTableCongruence
@[expose] public section

/-! Actual candidate families/factors construct the native identity tables.
Joint fixation identifies their complete partial/full tables and honest
polynomials for every retained native prior, rather than assuming a chosen
honest polynomial or pointwise evaluation certificate. -/
namespace FormalProof4FHE.HasteBoots.CandidateIdentityTables
open InputIndexedOracle (World)
open OracleProgram (Program)
open NativeRootMessage (Digest)
open JobReferenceCandidate (Candidate)
open JobReferenceFixation (Fixed)
open NativeFieldWire (goldExtensionValue)
noncomputable section

def partialTables {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (radius : ℕ) :=
  LookupIdentityCausalReduction.partialTables candidate.selection.job.view
    (candidate.selection.sources dummy radius) (candidate.selection.helpers dummy radius)

def fullTables {A : Type} {program : Program A} {position : ℕ} {world : World}
    (candidate : Candidate program position world) (dummy : Digest) (radius : ℕ) :=
  LookupIdentityCausalReduction.fullTables candidate.selection.job.view
    (candidate.selection.sources dummy radius) (candidate.selection.helpers dummy radius)

structure Alignment {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) : Prop where
  padding : left.selection.origin.padding = right.selection.origin.padding
  rows : left.selection.body.sourceVariables = right.selection.body.sourceVariables
  helperPadding : AllocatedLookupTables.helperPadding (ctx := left.selection.ctx) = AllocatedLookupTables.helperPadding (ctx := right.selection.ctx)
  request : (left.selection.origin.ready.jobs.get left.selection.index).tag.request = (right.selection.origin.ready.jobs.get right.selection.index).tag.request
  point : List.ofFn left.selection.job.view.eqPoint = List.ofFn right.selection.job.view.eqPoint
  compression : (left.selection.origin.ready.jobs.get left.selection.index).output.y = (right.selection.origin.ready.jobs.get right.selection.index).output.y
  offset : (left.selection.origin.ready.jobs.get left.selection.index).output.r = (right.selection.origin.ready.jobs.get right.selection.index).output.r

theorem alignment {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy radius) : Alignment left right := by
  obtain ⟨⟨agree,_⟩,_,compression,offset,point⟩ := fixed
  have registry := left.selection.registry.symm.trans (agree.1.trans right.selection.registry)
  have helper := left.selection.helper.symm.trans (agree.2.1.trans right.selection.helper)
  have requests := left.selection.requests.symm.trans (agree.2.2.1.trans right.selection.requests)
  have dimensions := OriginalJobOrdinal.dimensions left.selection.origin right.selection.origin registry
  exact ⟨dimensions.2,dimensions.1,congrArg (fun parameters => parameters.width.val-3) helper,
    OriginalJobOrdinal.request left.selection.origin right.selection.origin requests left.selection.index right.selection.index ordinal,
    left.point_native.symm.trans (point.symm.trans right.point_native),
    left.compression_native.symm.trans (compression.symm.trans right.compression_native),
    left.offset_native.symm.trans (offset.symm.trans right.offset_native)⟩

theorem partial_tables {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy radius) :
    HEq (partialTables left dummy radius) (partialTables right dummy radius) := by
  have aligned := alignment left right dummy radius ordinal fixed
  exact LookupIdentityTableCongruence.partial_tables left.selection.job.view.eqPoint right.selection.job.view.eqPoint _ _ _ _
    (NativeScalarQueryShape.checked_power _ _ _ left.selection.job.view.shape) (NativeScalarQueryShape.checked_power _ _ _ right.selection.job.view.shape)
    _ _ _ _ aligned.padding aligned.rows aligned.helperPadding (congrArg NativeSharedLookupStatement.Request.columns aligned.request)
    aligned.point aligned.compression (congrArg (fun request => request.terminal.logicalLength.val) aligned.request) fixed.2.1.1 fixed.2.1.2

theorem full_tables {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy radius) :
    HEq (fullTables left dummy radius) (fullTables right dummy radius) := by
  have aligned := alignment left right dummy radius ordinal fixed
  exact LookupIdentityTableCongruence.full_tables left.selection.job.view.eqPoint right.selection.job.view.eqPoint _ _ _ _
    (NativeScalarQueryShape.checked_power _ _ _ left.selection.job.view.shape) (NativeScalarQueryShape.checked_power _ _ _ right.selection.job.view.shape)
    _ _ _ _ aligned.padding aligned.rows aligned.helperPadding (congrArg NativeSharedLookupStatement.Request.columns aligned.request)
    aligned.point aligned.offset aligned.compression fixed.2.1.1 fixed.2.1.2

theorem partial_honest {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy radius)
    (prior : List NativeGoldExtensionArithmetic.Word) :
    ScalarNativeSourceHealing.honest ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (left.selection.origin.ready.jobs.get left.selection.index).output.r))
      ExtensionLookupIdentity.partialIndices (NativeScalarQueryShape.laneBits (3+left.selection.origin.padding)+left.selection.body.sourceVariables)
      (partialTables left dummy radius) prior =
    ScalarNativeSourceHealing.honest ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (right.selection.origin.ready.jobs.get right.selection.index).output.r))
      ExtensionLookupIdentity.partialIndices (NativeScalarQueryShape.laneBits (3+right.selection.origin.padding)+right.selection.body.sourceVariables)
      (partialTables right dummy radius) prior := by
  have aligned := alignment left right dummy radius ordinal fixed
  exact LookupIdentityTableCongruence.honest _ _ _ _ _ _ (by rw [aligned.padding,aligned.rows])
    (partial_tables left right dummy radius ordinal fixed) (by rw [aligned.offset]) prior

theorem full_honest {A : Type} {program : Program A} {position : ℕ} {world other : World}
    (left : Candidate program position world) (right : Candidate program position other) (dummy : Digest) (radius : ℕ)
    (ordinal : left.selection.index.val = right.selection.index.val) (fixed : Fixed left right dummy radius)
    (prior : List NativeGoldExtensionArithmetic.Word) :
    ScalarNativeSourceHealing.honest ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (NativeScalarQueryShape.laneBits (3+left.selection.origin.padding)+left.selection.body.sourceVariables) (fullTables left dummy radius) prior =
    ScalarNativeSourceHealing.honest ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (NativeScalarQueryShape.laneBits (3+right.selection.origin.padding)+right.selection.body.sourceVariables) (fullTables right dummy radius) prior := by
  have aligned := alignment left right dummy radius ordinal fixed
  exact LookupIdentityTableCongruence.honest _ _ _ _ _ _ (by rw [aligned.padding,aligned.rows])
    (full_tables left right dummy radius ordinal fixed) rfl prior

end
end FormalProof4FHE.HasteBoots.CandidateIdentityTables
