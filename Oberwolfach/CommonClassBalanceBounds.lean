module

public import Oberwolfach.CommonClassBalanceGeometry

@[expose] public section

/-! Quantitative loss in the actual root-preserving class construction.
All sizes and errors are measured at the original ambient order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

 theorem changed_symm_eq (A B:Finset V):changed A B=changed B A:=by
  ext v
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,or_comm]

 theorem common_class_balance_bounds (π:Equiv.Perm V) (m:ℕ) (hm:1≤m)
    (A₀ B₀ I ZK ZO:Finset V) (hAB:Disjoint A₀ (B₀∪ZO))
    (hZA:ZK⊆A₀) (hZI:Disjoint (ZK∪ZO) I) (hsep:Disjoint ZK (ZO.image π.symm))
    (hZ:ZO.card=m*ZK.card) (n q ε f:ℝ) (hn:0≤n) (hε:0≤ε)
    (hAc:|(A₀.card:ℝ)-q*n|≤ε*n) (hBc:|(B₀.card:ℝ)-m*q*n|≤ε*n)
    (hIc:(I.card:ℝ)≤ε*n) (hOc:((B₀∩A₀.image π).card:ℝ)≤ε*n) (hZc:(ZO.card:ℝ)≤f):
    ∃ A B:Finset V,ZK⊆A∧ZO⊆B∧A⊆A₀∧B⊆B₀∪ZO∧Disjoint A B∧
      Disjoint (A∪B) I∧Disjoint B (A.image π)∧B.card=m*A.card∧
      (((changed A₀ A).card:ℝ)+(changed B₀ B).card≤4*(m+1)*ε*n+2*(m+1)*f+(m+1))∧
      q*n-ε*n-(((changed A₀ A).card:ℝ)+(changed B₀ B).card)≤A.card:=by
  obtain ⟨A,B,hZA',hZO',hAA,hBB,hI,hπ,hcard,hL⟩:=
    common_class_balanced_subsets π A₀ B₀ I ZK ZO m hm hZA hZI hsep hZ
  rw [changed_symm_eq A A₀,changed_symm_eq B B₀] at hL
  have himb:|(B₀.card:ℝ)-m*A₀.card|≤(m+1)*ε*n:=by
    calc
      _ = |((B₀.card:ℝ)-m*q*n)-m*((A₀.card:ℝ)-q*n)|:=by congr 1;ring
      _ ≤ |(B₀.card:ℝ)-m*q*n|+|m*((A₀.card:ℝ)-q*n)|:=abs_sub _ _
      _ ≤ _:=by rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤m by positivity)];nlinarith only [hAc,hBc]
  have hfinal:((changed A₀ A).card:ℝ)+(changed B₀ B).card≤4*(m+1)*ε*n+2*(m+1)*f+(m+1):=by
    have hsum:(B₀∩A₀.image π).card+2*(I.card:ℝ)+2*ZO.card≤3*ε*n+2*f:=by linarith
    have hmR:(0:ℝ)≤m:=by positivity
    nlinarith only [hL,himb,hsum,hmR]
  have hsize:q*n-ε*n-(((changed A₀ A).card:ℝ)+(changed B₀ B).card)≤A.card:=by
    have hc:=card_difference_le_changed A₀ A
    have ha: q*n-ε*n≤A₀.card:=by linarith only [(abs_le.mp hAc).1]
    have hh: (A₀.card:ℝ)-A.card≤(changed A₀ A).card:=(le_abs_self _).trans hc
    have hnon:(0:ℝ)≤(changed B₀ B).card:=by positivity
    linarith
  exact ⟨A,B,hZA',hZO',hAA,hBB,hAB.mono hAA hBB,hI,hπ,hcard,hfinal,hsize⟩

end Oberwolfach
