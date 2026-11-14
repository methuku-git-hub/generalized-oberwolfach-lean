module

public import Oberwolfach.FiniteSumProduct

@[expose] public section
/-! Combining independent outcomes on disjoint coordinate sets recovers the
original product law over their disjoint union. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def combineSumCoordinates {A B:Type} {S:A⊕B→Type}
    (x:∀ a,S (Sum.inl a)) (y:∀ b,S (Sum.inr b)) : ∀ e,S e:=
  fun e=>Sum.rec x y e

theorem finiteLaw_product_sum_law {A B:Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {S:A⊕B→Type} [∀ e,Fintype (S e)] (μ:∀ e,FiniteLaw (S e)):
    ((FiniteLaw.pi (fun b=>μ (Sum.inr b))).prod (FiniteLaw.pi (fun a=>μ (Sum.inl a)))).map
      (fun z=>combineSumCoordinates z.2 z.1)=FiniteLaw.pi μ:=by
  apply finiteLaw_ext
  intro σ
  let E:=fun (y:∀ b,S (Sum.inr b)) (x:∀ a,S (Sum.inl a))=>combineSumCoordinates x y=σ
  have hp:=finiteLaw_pi_sum_probability μ E
  have hleft:(FiniteLaw.pi μ).probability (fun τ=>E (fun b=>τ (Sum.inr b)) (fun a=>τ (Sum.inl a)))=
      (FiniteLaw.pi μ).probability (fun τ=>τ=σ):=by
    apply congrArg (FiniteLaw.probability (FiniteLaw.pi μ))
    funext τ
    apply propext
    have hh:combineSumCoordinates (fun a=>τ (Sum.inl a)) (fun b=>τ (Sum.inr b))=τ:=by
      funext e
      cases e <;> rfl
    simp [E,hh]
  rw [hleft] at hp
  have hmap:=finiteLaw_map_probability
    ((FiniteLaw.pi (fun b=>μ (Sum.inr b))).prod (FiniteLaw.pi (fun a=>μ (Sum.inl a))))
    (fun z=>combineSumCoordinates z.2 z.1) (fun x=>x=σ)
  have heq:=hmap.trans hp.symm
  simpa [FiniteLaw.probability,eq_comm,E] using heq
end Oberwolfach
