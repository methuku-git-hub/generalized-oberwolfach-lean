module

public import Oberwolfach.OrdinaryTriangleCoverNormalizedRates
public import Oberwolfach.OrdinaryRootCoverSharpReferenceExists

@[expose] public section
/-! Put the actual sharp triangle reference into the rate form used by the
cleanup certificate, retaining its own root-cover witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_sharp_reference_normalized_rates
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
    (P Q F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (J W:Finset U) (k:ℕ)
    (ξroot κ lam ellCap finishCap bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ)
    (hnV:0<Fintype.card V) (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hξ:0≤ξroot) (hκ:0≤κ) (hlam:0≤lam) (hellCap:0≤ellCap) (hfinish:0≤finishCap)
    (hell:max (18*κ+3*lam) ((3*κ+lam)*3)≤ellCap) (hcover:10*ξroot≤finishCap):
    let cover:=10*ξroot*I.card;
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*κ*Fintype.card V*3+(T.card:ℝ)*3);
    OrdinaryRootCoverSharpReferenceExists P Q F H I T J W 3 k (by decide)
      cover ell bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c→
    ∃ηrate ellrate:ℝ,0≤ηrate ∧ ηrate≤finishCap ∧ 0≤ellrate ∧ ellrate≤ellCap ∧
      OrdinaryRootCoverSharpReferenceExists P Q F H I T J W 3 k (by decide)
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c :=by
  intro cover ell href
  have hIV:(I.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ I
  have hnVr:0<(Fintype.card V:ℝ):=by exact_mod_cast hnV
  obtain ⟨ηrate,ellrate,hη0,hηcap,hell0,hellcap,hcoverEq,hellEq⟩:=
    ordinary_triangle_cover_normalized_rates (Fintype.card V) (Fintype.card U) I.card T.card W.card
      ξroot κ lam ellCap finishCap hnVr (by positivity) (by positivity) hIV (by positivity) (by positivity)
      hroot hξ hκ hlam hellCap hfinish hell hcover
  refine ⟨ηrate,ellrate,hη0,hηcap,hell0,hellcap,?_⟩
  have hcard:(Fintype.card (V⊕U):ℝ)=Fintype.card V+Fintype.card U:=by simp
  rw [hcard,←hcoverEq,←hellEq]
  exact href
end Oberwolfach
