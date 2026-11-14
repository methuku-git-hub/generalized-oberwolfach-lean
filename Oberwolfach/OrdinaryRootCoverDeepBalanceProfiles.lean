module

public import Oberwolfach.OrdinaryRootCoverSelfEdits
public import Oberwolfach.OrdinaryRootCoverRemainderFacts
public import Oberwolfach.OrdinaryRestrictedBalanceOfDeepBalance
public import Oberwolfach.OrdinaryNonrootBalancedDeepProfiles

@[expose] public section
/-! If the current host is balanced across the protected deep pair, the
root-cover remainder has controlled profiles without charging the full size
of that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_deep_balance_profiles (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell b c deep:ℝ) (hell:0≤ell)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    (∀v:A,|(((Q'.induce (A:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val)).card|≤deep+3*ell) ∧
    (∀v:A,|((spanningRestriction (Q'.induce (A:Set V)) Xf).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>H' v.val u.val∧v∈Xf∧u∈Zf)).card|≤b+3*ell+(deep+3*ell)) ∧
    (∀v:A,v∉Xf→|((((Q'.induce (A:Set V)).neighborFinset v)∩Xf).card:ℝ)-
      2*(Zf.filter (fun u=>H' v.val u.val)).card|≤c+3*ell+(deep+3*ell)):=by
  intro A B Xf Zf Q' H'
  have he:=ordinary_root_cover_self_edits Q F H X T Z W r η ell D
  have hR:∀v∉T,((changed (Q'.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤ell:=by
    intro v hv;convert he.1 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hH:∀v∉T,((changed (Finset.univ.filter (H' v)) (Finset.univ.filter (H v))).card:ℝ)≤ell:=by
    intro v hv;convert he.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hd:∀v∉T,|((Q'.neighborFinset v∩T).card:ℝ)-2*(W.filter (H' v)).card|≤deep+3*ell:=by
    intro v hv
    have hbase:=hdeep v hv
    have hEq:W.filter (H v)=(Finset.univ.filter (H v))∩W:=by ext u;simp [and_comm]
    have hEq':W.filter (H' v)=(Finset.univ.filter (H' v))∩W:=by ext u;simp [and_comm]
    rw [hEq] at hbase
    rw [hEq']
    exact ordinary_cross_balance_change (Q'.neighborFinset v) (Q.neighborFinset v) T
      (Finset.univ.filter (H' v)) (Finset.univ.filter (H v)) W deep ell hbase (hR v hv) (hH v hv)
  have hb:∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card:=by
    convert (ordinary_root_cover_remainder_facts Q F H X T Z W r η ell hbal hdiv D.toOrdinaryRootCoverData).1 using 1 <;>
      congr! 10 <;> exact Subsingleton.elim _ _
  have hf:=ordinary_restricted_near_balance_of_deep_balance Q' H' T W (by
    intro v;convert hb v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (deep+3*ell) (by
    intro v hv;convert hd v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hp:=ordinary_nonroot_balanced_deep_profiles Q' Q H' H X T Z W ell b c (deep+3*ell)
    hell hTX hWZ (by intro v hv;convert hR v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hH v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hd v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hinner hcross
  refine ⟨?_,?_,?_⟩
  · convert hf using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hp.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hp.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
