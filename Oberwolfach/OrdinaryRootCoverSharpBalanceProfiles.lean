module

public import Oberwolfach.OrdinaryRootCoverSharpInnerBalance
public import Oberwolfach.OrdinaryRootCoverSharpCrossBalance

@[expose] public section
/-! Sharp nonroot balance profiles retain the actual deep-cross tests and
the cover's low-load crossing bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_sharp_balance_profiles
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell b c deep loss:ℝ)
    (hη:0≤η) (hb:0≤b) (hdeep0:0≤deep) (hTX:T⊆X) (hWZ:W⊆Z)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c)
    (hdel:∀v∉X,|((D.rim.neighborFinset v∩(X\T)).card:ℝ)-
      2*((Z\W).filter (D.spokes v)).card|≤loss):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    (∀v:A,|(((Q'.induce (A:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val)).card|≤deep+2*η) ∧
    (∀v:A,|((spanningRestriction (Q'.induce (A:Set V)) Xf).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val∧v∈Xf∧u∈Zf)).card|≤b+deep+4*η) ∧
    (∀v:A,v∉Xf→|((((Q'.induce (A:Set V)).neighborFinset v)∩Xf).card:ℝ)-
      2*(Zf.filter (fun u=>H' v.val u.val)).card|≤c+deep+loss):=by
  intro A B Xf Zf Q' H'
  have hi:∀v∈X,v∉T→|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep:=by
    intro v hv hvt;exact hdeep v hvt
  have ho:∀v∉X,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep:=by
    intro v hv;exact hdeep v (fun ht=>hv (hTX ht))
  have hf:=ordinary_root_cover_sharp_full_balance Q F H X T Z W r η ell deep hη hdeep0 hTX hWZ D hbal hdiv hi
  have hn:=ordinary_root_cover_sharp_inner_balance Q F H X T Z W r η ell b deep hη hb hdeep0 hTX hWZ D hinner hi
  have hc:=ordinary_root_cover_sharp_cross_balance Q F H X T Z W r η ell c deep loss hTX hWZ D hcross ho hdel
  refine ⟨?_,?_,?_⟩
  · intro v;convert hf v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v;convert hn v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv;convert hc v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
