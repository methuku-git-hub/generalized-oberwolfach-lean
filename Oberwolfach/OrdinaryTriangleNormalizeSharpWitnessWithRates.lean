module

public import Oberwolfach.OrdinaryTriangleCoverNormalizedRates
public import Oberwolfach.OrdinaryTriangleSharpInnerFixedPacking

@[expose] public section
/-! Normalize the budgets in a sharp triangle reference without changing the
actual nonroot cover or its physical host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_normalize_sharp_witness_with_rates
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (k:ℕ) (hk:4≤k)
    (ξ aLoad lam ellCap finishCap:ℝ)
    (hnV:0<Fintype.card V) (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hξ:0≤ξ) (ha:0≤aLoad) (hlam:0≤lam) (hellCap:0≤ellCap) (hfinish:0≤finishCap)
    (hell:max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap) (hcover:10*ξ≤finishCap)
    (b₁ c₁ deep crossLoss α ω βparent βout b B h δref εparent εstar ηpack ξreserve ζ p εout f binner c:ℝ):
    let cover:=10*ξ*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card V*3+(T.card:ℝ)*3);
    ∀(D:OrdinaryRootCoverNonrootData Q F H X T Z W 3 cover ell),
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss D α ω βparent βout b B h δref εparent εstar ηpack ξreserve ζ p εout f binner c)→
    ∃ηrate ellrate:ℝ,0≤ηrate ∧ ηrate≤finishCap ∧ 0≤ellrate ∧ ellrate≤ellCap ∧
    cover=ηrate*Fintype.card (V⊕U) ∧ ell=ellrate*Fintype.card (V⊕U) ∧
    ∃D':OrdinaryRootCoverNonrootData Q F H X T Z W 3
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)),
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W 3 k (by omega)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₁ c₁ deep crossLoss D'
      α ω βparent βout b B h δref εparent εstar ηpack ξreserve ζ p εout f binner c) :=by
  intro cover ell D href
  have hnV':(0:ℝ)<Fintype.card V:=by exact_mod_cast hnV
  have hIV:(X.card:ℝ)≤Fintype.card V:=by exact_mod_cast X.card_le_univ
  obtain ⟨ηrate,ellrate,hη,hηcap,hell0,hellcap,hcovereq,helleq⟩:=
    ordinary_triangle_cover_normalized_rates (Fintype.card V) (Fintype.card U) X.card T.card W.card
      ξ aLoad lam ellCap finishCap hnV' (by positivity) (by positivity) hIV (by positivity) (by positivity)
      hroot hξ ha hlam hellCap hfinish hell hcover
  have hN:(Fintype.card V:ℝ)+Fintype.card U=Fintype.card (V⊕U):=by simp
  rw [hN] at hcovereq helleq
  refine ⟨ηrate,ellrate,hη,hηcap,hell0,hellcap,hcovereq,helleq,?_⟩
  rw [←hcovereq,←helleq]
  exact ⟨D,href⟩
end Oberwolfach
