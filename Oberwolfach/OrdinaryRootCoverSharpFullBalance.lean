module

public import Oberwolfach.OrdinaryRootCoverRemainderFacts
public import Oberwolfach.OrdinaryRestrictedBalanceOfDeepBalance
public import Oberwolfach.OrdinaryPhysicalCostCrossBound

@[expose] public section
/-! At vertices outside the inner pair the root boundary is completely
covered. At vertices inside it, the change to the deep cross-discrepancy
is paid only by the cover's inner degree, not its global nonroot load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_sharp_deep_cross
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell deep:ℝ)
    (hη:0≤η) (hdeep0:0≤deep) (hTX:T⊆X) (hWZ:W⊆Z)
    (A:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (hdeep:∀v∈X,v∉T→|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep):
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    ∀v∉T,|((Q'.neighborFinset v∩T).card:ℝ)-2*(W.filter (H' v)).card|≤deep+2*η:=by
  intro Q' H' v hvT
  by_cases hvX:v∈X
  · have hc:=ordinary_physical_cost_cross_bound A.rim A.spokes X T Z W hTX hWZ v hvX η A.inner_degree
    exact ordinary_cross_balance_deletion_transfer_at Q A.rim H A.spokes T W v deep (2*η)
      A.rim_sub A.spoke_sub (hdeep v hvX hvT) hc
  · have hR:Q'.neighborFinset v∩T=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hwT:w∈T:=(Finset.mem_inter.mp hw).2
      have hvw:Q'.Adj v w:=(Q'.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1
      exact hvw.symm.2 (A.covers_rim w hwT v hvX hvw.symm.1)
    have hS:W.filter (H' v)=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have huW:u∈W:=(Finset.mem_filter.mp hu).1
      have hvu:H' v u:=(Finset.mem_filter.mp hu).2
      exact hvu.2 (A.covers_column u huW v hvX hvu.1)
    rw [hR,hS]
    simp only [Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
    linarith

theorem ordinary_root_cover_sharp_full_balance
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell deep:ℝ)
    (hη:0≤η) (hdeep0:0≤deep) (hTX:T⊆X) (hWZ:W⊆Z)
    (A:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∈X,v∉T→|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    ∀v:Vfree,|(((Q'.induce (Vfree:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:Ufree=>H' v.val u.val)).card|≤deep+2*η:=by
  intro Vfree Ufree Q' H'
  have hr:=ordinary_root_cover_remainder_facts Q F H X T Z W r η ell hbal hdiv A
  have hcross:=ordinary_root_cover_sharp_deep_cross Q F H X T Z W r η ell deep hη hdeep0 hTX hWZ A hdeep
  have hh:=ordinary_restricted_near_balance_of_deep_balance Q' H' T W
    (by intro v;convert hr.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (deep+2*η) (by intro v hv;convert hcross v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  intro v
  convert hh v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
