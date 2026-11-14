module

public import Oberwolfach.SupportedResourceStateRestriction

@[expose] public section
/-! Restricting the state by a physical eligibility predicate leaves the
active typed fiber of an eligible physical resource unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B:Type} [Fintype A] [DecidableEq A]

theorem physical_eligible_active_fiber (φ:A→B) (eligible:B→Prop) (σ:A→Bool)
    (x:B) (hx:eligible x):
    Finset.univ.filter (fun a=>φ a=x ∧ physicallyRestrictedState φ eligible σ a=true)=
      Finset.univ.filter (fun a=>φ a=x ∧ σ a=true) :=by
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ha,hs⟩
    exact ⟨ha,by simpa [physicallyRestrictedState,ha,hx] using hs⟩
  · rintro ⟨ha,hs⟩
    exact ⟨ha,by simpa [physicallyRestrictedState,ha,hx] using hs⟩
end Oberwolfach
