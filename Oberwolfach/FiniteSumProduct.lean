module

public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawMap

@[expose] public section

/-! Splitting a product experiment into two disjoint coordinate sets gives
exactly the product of their original laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_sum_probability
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {State : A⊕B → Type*} [∀ e,Fintype (State e)]
    (μ : ∀ e,FiniteLaw (State e))
    (E : (∀ b,State (Sum.inr b)) → (∀ a,State (Sum.inl a)) → Prop) :
    (FiniteLaw.pi μ).probability (fun σ=>E (fun b=>σ (Sum.inr b)) (fun a=>σ (Sum.inl a)))=
      ((FiniteLaw.pi (fun b=>μ (Sum.inr b))).prod (FiniteLaw.pi (fun a=>μ (Sum.inl a)))).probability
        (fun z=>E z.1 z.2) := by
  let e : (∀ x,State x) ≃ ((∀ b,State (Sum.inr b))×(∀ a,State (Sum.inl a))) :=
    { toFun := fun σ=>(fun b=>σ (Sum.inr b),fun a=>σ (Sum.inl a))
      invFun := fun z x=>Sum.rec z.2 z.1 x
      left_inv := by intro σ;funext x;cases x <;> rfl
      right_inv := by intro z;cases z;rfl }
  unfold FiniteLaw.probability
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  change (if E z.1 z.2 then ∏ a,(μ a).mass (Sum.rec z.2 z.1 a) else 0)=
    if E z.1 z.2 then (∏ b,(μ (Sum.inr b)).mass (z.1 b))*(∏ a,(μ (Sum.inl a)).mass (z.2 a)) else 0
  rw [Fintype.prod_sum_type]
  split_ifs <;> simp only [mul_comm]

end Oberwolfach
