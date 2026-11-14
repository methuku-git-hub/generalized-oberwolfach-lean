module

public import Oberwolfach.OrdinaryComplementReserveSizeInputs

@[expose] public section
/-! One common lower bound for the current inner domain supplies all size
and failure-budget inputs of the root-free triangle certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_local_sizes
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (X T:Finset V) (W:Finset U) (n₀ Nreserve Nclean Ninner Nsafe Norder:ℕ) (lam:ℝ)
    (hlam:lam≤1/4) (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hn₀:4*n₀≤X.card) (hreserve:4*Nreserve≤X.card) (hclean:Nclean≤X.card)
    (hinner:Ninner≤X.card) (hsafe:Nsafe≤X.card) (horder:Norder≤X.card) (hlarge:64≤X.card):
    n₀≤Fintype.card ↥(Finset.univ\T) ∧
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)) ∧
    Nclean≤Fintype.card (V⊕U) ∧ Nsafe≤Fintype.card (V⊕U) ∧ Norder≤Fintype.card (V⊕U) ∧
    Ninner≤X.card ∧ 32≤X.card ∧ 16≤Fintype.card V ∧
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^1≤(1/16:ℝ) ∧
    (1/16:ℝ)+2/(Fintype.card (V⊕U):ℝ)≤1/8 :=by
  have hXV:X.card≤Fintype.card V:=Finset.card_le_univ X
  have hV0:0≤(Fintype.card V:ℝ):=by positivity
  have hW0:0≤(W.card:ℝ):=by positivity
  have hT:(T.card:ℝ)≤(1/4:ℝ)*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_right hlam hV0
    linarith
  have hcomp:=ordinary_complement_reserve_size_inputs T W n₀ Nreserve Nclean hT
    (hn₀.trans hXV) (hreserve.trans hXV) (hclean.trans hXV) (hlarge.trans hXV)
  have hinj:Fintype.card V≤Fintype.card (V⊕U):=
    Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective
  exact ⟨hcomp.1,hcomp.2.1,hcomp.2.2.1,(hsafe.trans hXV).trans hinj,
    (horder.trans hXV).trans hinj,hinner,by omega,by omega,by simpa only [pow_one] using hcomp.2.2.2.1,hcomp.2.2.2.2⟩
end Oberwolfach
