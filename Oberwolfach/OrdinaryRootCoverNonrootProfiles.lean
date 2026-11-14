module

public import Oberwolfach.OrdinaryRootCoverSelfEdits
public import Oberwolfach.OrdinaryRootCoverRestrictedBalance
public import Oberwolfach.OrdinaryNonrootCrossBalance
public import Oberwolfach.OrdinaryNonrootInnerBalance

@[expose] public section
/-! The actual root-cover remainder supplies the full, inner and cross
near-balance profiles needed on the adaptive nonroot domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_nonroot_profiles (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell b c:ℝ) (hell:0≤ell)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    (∀v:A,|(((Q'.induce (A:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val)).card|≤(T.card:ℝ)+2*W.card) ∧
    (∀v:A,|((spanningRestriction (Q'.induce (A:Set V)) Xf).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val∧v∈Xf∧u∈Zf)).card|≤b+3*ell+T.card+2*W.card) ∧
    (∀v:A,v∉Xf→|((((Q'.induce (A:Set V)).neighborFinset v)∩Xf).card:ℝ)-
      2*(Zf.filter (fun u=>H' v.val u.val)).card|≤c+3*ell+T.card+2*W.card):=by
  intro A B Xf Zf Q' H'
  have he:=ordinary_root_cover_self_edits Q F H X T Z W r η ell D
  have hf:=ordinary_root_cover_restricted_balance Q F H X T Z W r η ell hbal hdiv D
  have hR:∀v∉T,((changed (Q'.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤ell:=by
    intro v hv
    convert he.1 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hH:∀v∉T,((changed (Finset.univ.filter (H' v)) (Finset.univ.filter (H v))).card:ℝ)≤ell:=by
    intro v hv
    convert he.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hi:=ordinary_nonroot_inner_balance Q' Q H' H X T Z W ell b hell (by
    intro v hv;convert hR v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by
    intro v hv;convert hH v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hinner
  have hc:=ordinary_nonroot_cross_balance Q' Q H' H X T Z W ell c (by
    intro v hv;convert hR v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by
    intro v hv;convert hH v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hcross
  refine ⟨?_,?_,?_⟩
  · convert hf using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hi using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
