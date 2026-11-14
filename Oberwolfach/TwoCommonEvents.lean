module

public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Two events under the same finite law, with their individual errors.
No independence assumption is required. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finiteLaw_two_events_lower {Ω:Type*} [Fintype Ω]
    (μ:FiniteLaw Ω) (P Q:Ω→Prop) (a b:ℝ)
    (hP:1-a≤μ.probability P) (hQ:1-b≤μ.probability Q):
    1-a-b≤μ.probability (fun σ=>P σ∧Q σ) :=
  (sub_le_sub_right hP b).trans (finiteLaw_good_intersection μ P Q b hQ)

end Oberwolfach
