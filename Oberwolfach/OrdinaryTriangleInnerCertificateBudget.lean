module

public import Oberwolfach.OrdinaryTriangleInnerLikelyCertificate

@[expose] public section
/-! A fixed positive slack in the reference failure probability absorbs
the extra inner-domain and sampled-cover failure terms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_inner_certificate_budget
    (A:Finset V) (loss:ℝ) (hA:32≤A.card) (hloss:loss≤1/8):
    (loss+2/(Fintype.card (V⊕U):ℝ))+1/(A.card:ℝ)≤1/4:=by
  have hAV:A.card≤Fintype.card V:=Finset.card_le_univ A
  have hVW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hAr:(32:ℝ)≤A.card:=by exact_mod_cast hA
  have hWr:(32:ℝ)≤Fintype.card (V⊕U):=by exact_mod_cast (hA.trans (hAV.trans hVW))
  have hApos:0<(A.card:ℝ):=by linarith
  have hWpos:0<(Fintype.card (V⊕U):ℝ):=by linarith
  have hAinv:1/(A.card:ℝ)≤1/32:=by
    apply (div_le_iff₀ hApos).2
    linarith
  have hWinv:2/(Fintype.card (V⊕U):ℝ)≤1/16:=by
    apply (div_le_iff₀ hWpos).2
    linarith
  linarith
end Oberwolfach
