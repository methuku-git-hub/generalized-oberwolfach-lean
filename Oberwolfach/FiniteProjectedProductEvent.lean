module

public import Oberwolfach.FiniteProductRegrouping
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Add an event measured on a projected first sample and the same second
    sample to an arbitrary event of the full product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_projected_product_event
    {Ω Ξ C:Type} [Fintype Ω] [Fintype Ξ] [Fintype C]
    (μ:FiniteLaw Ω) (μraw:FiniteLaw Ξ) (ν:FiniteLaw C) (f:Ω→Ξ)
    (hproj:μ.map f=μraw) (E:Ω×C→Prop) (A:Ξ×C→Prop) (a b:ℝ)
    (hE:1-a≤(μ.prod ν).probability E) (hA:1-b≤(μraw.prod ν).probability A):
    1-a-b≤(μ.prod ν).probability (fun z=>E z∧A (f z.1,z.2)):=by
  have hh:=finiteLaw_prod_map_left_probability μ ν f (fun x c=>A (x,c))
  rw [hproj] at hh
  have hA':1-b≤(μ.prod ν).probability (fun z=>A (f z.1,z.2)):=hh.symm ▸ hA
  exact finiteLaw_intersection_lower (μ.prod ν) E _ a b hE hA'
end Oberwolfach
