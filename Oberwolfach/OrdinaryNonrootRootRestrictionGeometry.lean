module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section
/-! A small root deletion preserves the hub-size gap and the inner-set
bounds needed for nonroot geometry. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_root_restriction_geometry
    (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (T X:Finset V) (W Z:Finset U) (ω lam eps ξ:ℝ)
    (hω:0<ω) (hξ:0≤ξ) (hlam:0≤lam) (hlam1:lam≤1/4) (hlamω:lam≤ω/2)
    (heps:0≤eps) (hepsξ:eps≤ξ/2) (hepsω:eps≤ξ*ω/2)
    (hn:0<Fintype.card V) (hU:ω*Fintype.card V≤Fintype.card U) (hupper:2*Fintype.card U≤Fintype.card V)
    (hroots:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hX:(X.card:ℝ)≤eps*Fintype.card V) (hZ:(Z.card:ℝ)≤eps*Fintype.card V):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    0<Fintype.card A ∧ 0<Fintype.card C ∧
    (ω/2)*Fintype.card A≤Fintype.card C ∧ Fintype.card C≤Fintype.card A ∧
    (Xf.card:ℝ)≤ξ*Fintype.card A ∧ (Zf.card:ℝ)≤ξ*Fintype.card A ∧
    (Zf.card:ℝ)≤ξ*Fintype.card C :=by
  intro A C Xf Zf
  have hA:Fintype.card A+T.card=Fintype.card V:=by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hC:Fintype.card C+W.card=Fintype.card U:=by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ W)
  have hAr:(Fintype.card A:ℝ)+T.card=Fintype.card V:=by exact_mod_cast hA
  have hCr:(Fintype.card C:ℝ)+W.card=Fintype.card U:=by exact_mod_cast hC
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hTr:(0:ℝ)≤T.card:=by positivity
  have hWr:(0:ℝ)≤W.card:=by positivity
  have hT:(T.card:ℝ)≤lam*Fintype.card V:=by linarith
  have hW:(W.card:ℝ)≤lam*Fintype.card V:=by linarith
  have hhalf:(Fintype.card V:ℝ)/2≤Fintype.card A:=by
    have hh:=mul_le_mul_of_nonneg_right hlam1 hnR.le
    linarith
  have hClo:(ω/2)*Fintype.card V≤Fintype.card C:=by
    have hh:=mul_le_mul_of_nonneg_right hlamω hnR.le
    linarith
  have hAp:0<Fintype.card A:=by exact_mod_cast (show (0:ℝ)<Fintype.card A by linarith)
  have hCp:0<Fintype.card C:=by
    have hh:(0:ℝ)<(ω/2)*Fintype.card V:=by positivity
    exact_mod_cast (show (0:ℝ)<Fintype.card C by linarith)
  have hupperR:(2:ℝ)*Fintype.card U≤Fintype.card V:=by exact_mod_cast hupper
  have hupper':Fintype.card C≤Fintype.card A:=by
    have hh:(Fintype.card C:ℝ)≤Fintype.card A:=by linarith
    exact_mod_cast hh
  have hAl:(ω/2)*Fintype.card A≤Fintype.card C:=by
    have ha:(Fintype.card A:ℝ)≤Fintype.card V:=by linarith
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans hClo
  have hXcard:Xf.card≤X.card:=by
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩
    have hs:Xf.image φ⊆X:=by intro v hv;obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv;simpa [Xf,φ] using hx
    simpa only [Finset.card_image_of_injective _ φ.injective] using Finset.card_le_card hs
  have hZcard:Zf.card≤Z.card:=by
    let φ:C↪U:=⟨Subtype.val,Subtype.val_injective⟩
    have hs:Zf.image φ⊆Z:=by intro u hu;obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hu;simpa [Zf,φ] using hx
    simpa only [Finset.card_image_of_injective _ φ.injective] using Finset.card_le_card hs
  have hXr:(Xf.card:ℝ)≤X.card:=by exact_mod_cast hXcard
  have hZr:(Zf.card:ℝ)≤Z.card:=by exact_mod_cast hZcard
  have hAξ:eps*Fintype.card V≤ξ*Fintype.card A:=by
    have hh:=mul_le_mul_of_nonneg_right hepsξ hnR.le
    have hh':=mul_le_mul_of_nonneg_left hhalf hξ
    nlinarith only [hh,hh']
  have hCξ:eps*Fintype.card V≤ξ*Fintype.card C:=by
    have hh:=mul_le_mul_of_nonneg_right hepsω hnR.le
    have hh':=mul_le_mul_of_nonneg_left hClo hξ
    nlinarith only [hh,hh']
  exact ⟨hAp,hCp,hAl,hupper',hXr.trans (hX.trans hAξ),hZr.trans (hZ.trans hAξ),hZr.trans (hZ.trans hCξ)⟩
end Oberwolfach
