module

public import Oberwolfach.ProductFailureBounds
public import Oberwolfach.FiniteProductSwap

@[expose] public section
/-! A bound uniform in the first-stage outcome remains valid after taking an
independent product; no uniformity over sample-dependent interval sets is
assumed without conditioning. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_product_uniform_conditional_event
    {A B:Type} [Fintype A] [Fintype B] (μ:FiniteLaw A) (ν:FiniteLaw B)
    (E:B→A→Prop) (δ:ℝ) (h:∀b,1-δ≤μ.probability (E b)):
    1-δ≤(μ.prod ν).probability (fun z=>E z.2 z.1):=by
  have heq:(μ.prod ν).probability (fun z=>E z.2 z.1)=
      ∑b,ν.mass b*μ.probability (E b):=by
    have hh:=finiteLaw_map_probability (μ.prod ν) Prod.swap (fun z=>E z.1 z.2)
    rw [finiteLaw_prod_swap] at hh
    have hh':(μ.prod ν).probability (fun z=>E z.2 z.1)=(ν.prod μ).probability (fun z=>E z.1 z.2):=by
      simpa only [Prod.swap] using hh.symm
    rw [hh',finiteLaw_prod_probability_slices]
  rw [heq]
  calc
    1-δ = ∑b,ν.mass b*(1-δ):=by rw [←Finset.sum_mul,ν.total,one_mul]
    _ ≤ ∑b,ν.mass b*μ.probability (E b):=by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (h b) (ν.nonneg b)
end Oberwolfach
