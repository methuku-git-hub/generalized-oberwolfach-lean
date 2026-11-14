module

public import Oberwolfach.ExtendingListPhysicalDeletion
public import Oberwolfach.MarkedResourceRimGraph

@[expose] public section
/-! The selected fixed reservoir can be removed from every extending list
at a cost proportional to its actual number of physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

theorem long_reserve_avoiding_extending_lists
    (D:V→V→Prop) (Lists:U→Finset V) (C:Finset (Finset V⊕(V×U)))
    (β lam ρ:ℝ) (hlam:0≤lam) (hρ:0≤ρ)
    (hC:(C.card:ℝ)≤ρ*Fintype.card V) (hmargin:lam+2*ρ≤β)
    (hext:∀u,IsExtendingList D (Lists u) β):
    ∀u,IsExtendingList (fun x y=>D x y ∧ ¬(markedResourceRimGraph C).Adj x y) (Lists u) lam:=by
  intro u
  have hD:∀x,((markedResourceRimGraph C).degree x:ℝ)≤ρ*Fintype.card V:=by
    intro x
    have hh:((markedResourceRimGraph C).degree x:ℝ)≤C.card:=by
      exact_mod_cast markedResourceRimGraph_degree_le C x
    exact hh.trans hC
  apply extending_list_after_physical_deletion D (markedResourceRimGraph C) (Lists u)
    β lam (ρ*Fintype.card V) hlam (by positivity) hD ?_ (hext u)
  have hn:(0:ℝ)≤Fintype.card V:=by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmargin hn]
end Oberwolfach
