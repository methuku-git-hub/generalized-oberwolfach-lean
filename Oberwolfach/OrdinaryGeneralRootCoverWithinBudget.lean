module

public import Oberwolfach.OrdinaryGeneralRootCoverBudget
public import Oberwolfach.OrdinaryNonrootWheelCoverData

@[expose] public section
/-! The actual general-wheel root cover fits the static reference geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_general_root_cover_within_budget
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (Z W:Finset U)
    (ξroot κ γ lam ηbal ε:ℝ)
    (hTI:T⊆I) (hWZ:W⊆Z)
    (hcover:OrdinaryNonrootWheelCoverResult m 0 ξroot κ Q F H I T Z W)
    (hγ:0<γ) (hκ:0≤κ) (hlam:0≤lam) (hlam1:lam≤1/4) (hη:0≤ηbal) (hε:0≤ε)
    (hI:(I.card:ℝ)≤ε*Fintype.card V) (hroots:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hκcap:κ≤γ/(1000*((m:ℝ)+2))) (hlamcap:lam≤γ/(1000*((m:ℝ)+2))) (hbalcap:ηbal*ε≤γ/8):
    let A:=Finset.univ\T;
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    let bin:=ηbal*I.card;let f:ℝ:=T.card+2*W.card;let binner:=bin+3*ell+f;
    Nonempty (OrdinaryRootCoverNonrootData Q F H I T Z W (m+1) (10*ξroot*I.card) ell) ∧
    0≤ell ∧ 0≤bin ∧ 0≤f ∧ 0≤binner ∧
    f≤γ*Fintype.card A ∧ binner≤γ*Fintype.card A ∧ ell≤γ*Fintype.card A :=by
  intro A ell bin f binner
  have hA:Fintype.card A+T.card=Fintype.card V:=by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hAr:(Fintype.card A:ℝ)+T.card=Fintype.card V:=by exact_mod_cast hA
  have hN:(0:ℝ)≤Fintype.card V:=by positivity
  have hhalf:(Fintype.card V:ℝ)/2≤Fintype.card A:=by
    have ht:(0:ℝ)≤T.card:=by positivity
    have hw:(0:ℝ)≤W.card:=by positivity
    have hh:=mul_le_mul_of_nonneg_right hlam1 hN
    linarith
  have hbudget:=ordinary_general_root_cover_budget m γ κ lam ηbal ε (Fintype.card V) (Fintype.card A)
    I.card T.card W.card hγ hκ hlam hη hε hN hhalf (by positivity) hI (by positivity) (by positivity)
    hroots hκcap hlamcap hbalcap
  have hdata:=ordinary_nonroot_wheel_cover_data m 0 ξroot κ Q F H I T Z W hTI hWZ hcover
  have hdata':Nonempty (OrdinaryRootCoverNonrootData Q F H I T Z W (m+1) (10*ξroot*I.card) ell):=by
    convert hdata using 1 <;> norm_num [ell] <;> push_cast <;> ring
  exact ⟨hdata',hbudget⟩
end Oberwolfach
