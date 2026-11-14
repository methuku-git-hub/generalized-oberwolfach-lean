module

public import Oberwolfach.MixedFreshParentDataInsideRoots

@[expose] public section
/-! The supplied hub and endpoint neighborhood data give uniform linear
lower bounds for the two base classes on the physical scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J K:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

theorem mixed_fresh_inside_parent_class_sizes (γ κ b B ε η:ℝ) (hγ:0≤γ) (hκ:0≤κ)
    (Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W) (T:J→Finset V) (S U:K→Finset W)
    (data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F P B₀ e T S U)
    (hVW:(Fintype.card W:ℝ)≤2*Fintype.card V):
    (∀j,min (κ/2) γ*Fintype.card W≤((T j).card:ℝ)) ∧
    (∀k,min (κ/2) γ*Fintype.card W≤((U k).card:ℝ)):=by
  have hmin:0≤min (κ/2) γ:=le_min (by positivity) hγ
  refine ⟨?_,?_⟩
  · intro j
    have h1:=mul_le_mul_of_nonneg_left hVW hmin
    have h2:=mul_le_mul_of_nonneg_right (min_le_left (κ/2) γ) (Nat.cast_nonneg (Fintype.card V))
    have hh:=data.hub_size j
    nlinarith only [h1,h2,hh]
  · intro k
    have h1:=mul_le_mul_of_nonneg_right (min_le_right (κ/2) γ) (Nat.cast_nonneg (Fintype.card W))
    exact h1.trans (data.endpoint_neighborhoods k).indices
end Oberwolfach
