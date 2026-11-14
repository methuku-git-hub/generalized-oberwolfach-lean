module

public import Oberwolfach.OrdinaryCycleCountBounds

@[expose] public section

/-! A nonnegative sum over unordered pairs is at most the sum over ordered
pairs. This allows actual graph degree bounds to control a physical-edge sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem sum_sym2_le_ordered {V : Type*} [Fintype V] (f : Sym2 V → ℝ)
    (hf : ∀ e,0≤f e) : (∑ e,f e)≤∑ x,∑ y,f s(x,y) := by
  let pick (e : Sym2 V) : V×V := Classical.choose (Sym2.mk_surjective e)
  have hp (e : Sym2 V) : s((pick e).1,(pick e).2)=e := Classical.choose_spec (Sym2.mk_surjective e)
  have hi : Function.Injective pick := by
    intro e g h
    rw [← hp e,← hp g,h]
  have hh := finite_injective_sum_le pick hi (fun p : V×V=>f s(p.1,p.2)) (fun p=>hf _)
  simpa only [hp,Fintype.sum_prod_type] using hh

end Oberwolfach
