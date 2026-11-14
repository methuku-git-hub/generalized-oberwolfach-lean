module

public import Oberwolfach.OrdinaryNonrootParentCuts
public import Oberwolfach.OrdinaryNonrootCardinalBounds

@[expose] public section
/-! Explicitly choose the restricted cut threshold using only the relative
sizes of the removed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_cutoff_margins (T:Finset V) (W:Finset U) (δ:ℝ)
    (hδ:0≤δ) (hδ1:δ<1)
    (hT:(T.card:ℝ)≤δ*Fintype.card V) (hW:(W.card:ℝ)≤δ*Fintype.card U):
    0<1-δ ∧
    (1-δ)*Fintype.card V≤(Fintype.card ↥(Finset.univ\T):ℝ) ∧
    (1-δ)*Fintype.card U≤(Fintype.card ↥(Finset.univ\W):ℝ) ∧
    1-2*δ≤(1-δ)*(1-2*(δ/2)):=by
  have hc:=ordinary_nonroot_cardinal_equalities T W
  have hV:((Fintype.card ↥(Finset.univ\T):ℕ):ℝ)+T.card=Fintype.card V:=by exact_mod_cast hc.1
  have hU:((Fintype.card ↥(Finset.univ\W):ℕ):ℝ)+W.card=Fintype.card U:=by exact_mod_cast hc.2
  refine ⟨by linarith,?_,?_,?_⟩
  · nlinarith only [hV,hT]
  · nlinarith only [hU,hW]
  · nlinarith [sq_nonneg δ]

theorem ordinary_nonroot_parent_cuts_with_margin
    (A:V→V→ℕ) (H:V→U→Prop) (T:Finset V) (W:Finset U) (δ h:ℝ)
    (hδ:0≤δ) (hδ1:δ<1) (hh:0≤h)
    (hV:0<Fintype.card ↥(Finset.univ\T)) (hU:0<Fintype.card ↥(Finset.univ\W))
    (hT:(T.card:ℝ)≤δ*Fintype.card V) (hW:(W.card:ℝ)≤δ*Fintype.card U)
    (hA:BipartiteLargeCut A δ h) (hH:BipartiteLargeCut (relationMultiplicity H) δ h):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    BipartiteLargeCut (fun (v w:Vfree)=>A v.val w.val) (δ/2) h ∧
    BipartiteLargeCut (relationMultiplicity (fun (v:Vfree) (u:Ufree)=>H v.val u.val)) (δ/2) h:=by
  have hm:=ordinary_nonroot_cutoff_margins T W δ hδ hδ1 hT hW
  exact ordinary_nonroot_parent_cuts A H T W (1-δ) δ (δ/2) h hm.1 hh hV hU hm.2.1 hm.2.2.1 hm.2.2.2 hA hH
end Oberwolfach
