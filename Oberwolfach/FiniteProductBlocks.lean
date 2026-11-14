module

public import Oberwolfach.FiniteProductRegrouping

@[expose] public section

/-! Grouping independent coordinates into blocks preserves the whole law,
not merely its marginal probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_blocks_probability {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {State : I→J→Type*} [∀ i j,Fintype (State i j)]
    (μ : ∀ i j,FiniteLaw (State i j)) (E : (∀ i j,State i j)→Prop) :
    (FiniteLaw.pi (fun a : I×J=>μ a.1 a.2)).probability (fun σ=>E (fun i j=>σ (i,j)))=
      (FiniteLaw.pi (fun i=>FiniteLaw.pi (μ i))).probability E := by
  let e : (∀ a : I×J,State a.1 a.2)≃(∀ i j,State i j) :=
    {toFun:=fun σ i j=>σ (i,j)
     invFun:=fun τ a=>τ a.1 a.2
     left_inv:=by intro σ;rfl
     right_inv:=by intro τ;rfl}
  unfold FiniteLaw.probability
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  change (if E σ then ∏ a : I×J,(μ a.1 a.2).mass (σ a.1 a.2) else 0)=
    if E σ then ∏ i,∏ j,(μ i j).mass (σ i j) else 0
  rw [Fintype.prod_prod_type]

end Oberwolfach
