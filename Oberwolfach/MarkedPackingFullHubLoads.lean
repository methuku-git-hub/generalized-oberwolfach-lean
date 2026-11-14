module

public import Oberwolfach.MarkedPackingLoadSpokeChanges

@[expose] public section

/-! For the identity hub embedding, the packing-domain load estimate
contains the potential-load estimate for every root in the whole host. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_packing_loads_on_all_hubs
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (D p k s₀ : ℝ) (weight : (Fin (m+1)→V)→ℝ) (a : Γ) (j : Color)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (η : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (h : MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j
      (Equiv.refl U) q s η σ H) :
    let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    ∀ root : ((V×V)⊕(V×V))⊕(Bool×V×U),
      rawMarkedWheelMarginal P π d p k q s a j root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η := by
  intro seed root hr
  have hh := h.2 root hr
  simpa only [rawMarkedRestrictHubs_rims, Equiv.refl_apply] using hh

end Oberwolfach
