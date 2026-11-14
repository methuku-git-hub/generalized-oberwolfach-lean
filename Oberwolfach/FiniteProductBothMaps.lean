module

public import Oberwolfach.FiniteLawProductMap

@[expose] public section
/-! A deterministic view of each independent factor has the product of the
pushforward laws. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_prod_map_both {Ω Γ Ξ Ζ:Type} [Fintype Ω] [Fintype Γ] [Fintype Ξ] [Fintype Ζ]
    (μ:FiniteLaw Ω) (ν:FiniteLaw Γ) (f:Ω→Ξ) (g:Γ→Ζ):
    (μ.prod ν).map (fun z=>(f z.1,g z.2))=(μ.map f).prod (ν.map g):=by
  apply finiteLaw_ext
  rintro ⟨x,y⟩
  simp only [FiniteLaw.map,FiniteLaw.prod,Fintype.sum_prod_type,Prod.mk.injEq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf:f a=x <;> by_cases hg:g b=y <;> simp [hf,hg]
end Oberwolfach
