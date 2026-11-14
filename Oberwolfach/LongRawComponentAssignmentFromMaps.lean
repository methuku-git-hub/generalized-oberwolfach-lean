module

public import Oberwolfach.LongRawOrdinaryComponentMapsProperty
public import Oberwolfach.LongRawComponentSizes
public import Oberwolfach.LongAssignedPaddedLengths

@[expose] public section
/-! Extract the single global component assignment and its exact length and
hub identities from the retained-test component maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_assignment_from_component_maps
    {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (hprop:LongRawOrdinaryComponentMapsProperty F π d m ℓ e M):
    ∃assign:(LongRawSelectedOrdinary π d m ℓ e M)↪(Σu,(F u).ConnectedComponent),
      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1):=by
  obtain ⟨assign,C,hC,f,hinto,honto,hR,hspoke,hdis⟩:=hprop
  have hsize:=long_raw_component_sizes_from_rim_cover F π d m ℓ e M C f hinto honto
  refine ⟨assign,?_,?_⟩
  · intro a
    exact (congrArg Sigma.fst (hC a)).symm
  · intro a
    have hh:=congrArg (fun x:Σu,(F u).ConnectedComponent=>Fintype.card x.2) (hC a)
    exact hh.symm.trans (hsize a)
end Oberwolfach
