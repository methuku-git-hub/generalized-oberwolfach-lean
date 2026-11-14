module

public import Oberwolfach.OrdinaryNonrootParentFields
public import Oberwolfach.OrdinaryNonrootCutoffMargins
public import Oberwolfach.OrdinaryNonrootConfigurationMargins
public import Oberwolfach.OrdinaryNonrootWeightMargins

@[expose] public section
/-! A small relative root set supplies the numerical hypotheses for the
restricted parent fields with explicit halved coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_nonroot_parent_from_relative_bounds
    (r:ℕ) (hr:3≤r) (k:ℕ) (hk:4≤k) (α β b B h δ ε lam:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop)
    (d:OrdinaryEditedParentFields r hr k α β b B h δ ε P Q F H)
    (T:Finset V) (W:Finset U) (hn:0<Fintype.card V) (hu0:0<Fintype.card U)
    (hu:Fintype.card U≤Fintype.card V) (hδ:0≤δ) (hδ1:δ<1)
    (hβ:0≤β) (hb:0≤b) (hB:0≤B) (hh:0≤h)
    (hT:(T.card:ℝ)≤δ*Fintype.card V) (hW:(W.card:ℝ)≤δ*Fintype.card U)
    (hWdegree:(W.card:ℝ)≤(β/2)*Fintype.card V)
    (hconfig:((T.card:ℝ)+W.card)*(r:ℝ)^2≤(β/2)*Fintype.card V)
    (hsize:(T.card:ℝ)+W.card≤lam*Fintype.card V):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    Nonempty (OrdinaryEditedParentFields r hr k α (β/2) (b*(1-δ)^(r-1)) B h (δ/2)
      (ε+lam*(r:ℝ)^4*B) (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
      (fun (v:A) (u:C)=>H v.val u.val)):=by
  intro A C
  have hm:=ordinary_nonroot_cutoff_margins T W δ hδ hδ1 hT hW
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have huR:(0:ℝ)<Fintype.card U:=by exact_mod_cast hu0
  have hA:0<Fintype.card A:=by
    have hhpos:0<(Fintype.card A:ℝ):=lt_of_lt_of_le (mul_pos hm.1 hnR) hm.2.1
    exact_mod_cast hhpos
  have hC:0<Fintype.card C:=by
    have hhpos:0<(Fintype.card C:ℝ):=lt_of_lt_of_le (mul_pos hm.1 huR) hm.2.2.1
    exact_mod_cast hhpos
  have hmn:(Fintype.card A:ℝ)≤Fintype.card V:=by
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val:A→V) Subtype.val_injective
  have hdegree:(β/2)*(Fintype.card A:ℝ)+(W.card:ℝ)≤β*Fintype.card V:=by
    have hh1:=mul_le_mul_of_nonneg_left hmn (show 0≤β/2 by linarith)
    linarith only [hh1,hWdegree]
  have hc:=ordinary_nonroot_configuration_margins r k hr hk β hβ T W hconfig
  have hs:=ordinary_nonroot_weight_scales (Fintype.card V) (Fintype.card A) (1-δ) b B (r-1)
    hnR hm.1 hmn hm.2.1 hb hB
  have he:=ordinary_nonroot_weight_error_margin (Fintype.card V) ((T.card:ℝ)+W.card) lam ((r:ℝ)^4) B
    hnR (by positivity) hB hsize
  apply ordinary_nonroot_parent_fields r hr k α β (β/2) b (b*(1-δ)^(r-1)) B B h δ (δ/2) ε
    (ε+lam*(r:ℝ)^4*B) (1-δ) P Q F H T W d hn hu hk hA hC hm.1 hh hb hB hm.2.1 hm.2.2.1 hm.2.2.2
    hdegree hc.1 hc.2 hs.1 hs.2
  nlinarith only [he]
end Oberwolfach
