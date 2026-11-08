namespace HasteBootsPhantomProof
open Aeneas Aeneas.Std Result
open hasteboots_phantom

theorem clone_exact {T : Type} (value : core.marker.PhantomData T) :
    core.marker.PhantomData.Insts.CoreCloneClone.clone value = ok value := rfl

theorem wrapper_exact {T : Type} (value : core.marker.PhantomData T) :
    phantom_clone value = ok value := rfl

theorem carrier_singleton {T : Type} (first second : core.marker.PhantomData T) :
    first = second := by
  cases first
  cases second
  rfl

end HasteBootsPhantomProof
