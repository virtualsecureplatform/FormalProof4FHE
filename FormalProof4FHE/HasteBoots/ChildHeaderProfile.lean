module
public import FormalProof4FHE.HasteBoots.NativeChildSeedView
@[expose] public section

/-! A complete canonical child header binds the trusted profile at slot 2.
This uses decoding of the entire framed input, not a later label search. -/
namespace FormalProof4FHE.HasteBoots.ChildHeaderProfile
open NativeChildSeedView (HasHeader seededFrames)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)

theorem compare {left right : NativeTranscript.Transcript} {lp rp ls rs : Digest} {ll lc rl rc : Input}
    (lh : HasHeader left lp ll lc ls) (rh : HasHeader right rp rl rc rs)
    (input : left.input = right.input) : lp = rp := by
  obtain ⟨leftSuffix,leftValid,leftBytes⟩ := lh
  obtain ⟨rightSuffix,rightValid,rightBytes⟩ := rh
  have leftDecoded := TranscriptFrame.decodeAll_encodeMany (seededFrames lp ll lc ls ++ leftSuffix) leftValid
  have rightDecoded := TranscriptFrame.decodeAll_encodeMany (seededFrames rp rl rc rs ++ rightSuffix) rightValid
  rw [← leftBytes,input] at leftDecoded
  rw [← rightBytes] at rightDecoded
  have frames := Option.some.inj (leftDecoded.symm.trans rightDecoded)
  have profile := congrArg (fun entries : List TranscriptFrame.Frame => entries[2]?) frames
  simp only [seededFrames,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at profile
  have message := congrArg TranscriptFrame.Frame.message (Option.some.inj profile)
  exact List.ofFn_injective message

end FormalProof4FHE.HasteBoots.ChildHeaderProfile
