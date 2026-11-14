module

public import Oberwolfach.ResidualMatchingCeilingBound
public import Oberwolfach.ResidualSubtypePositionBudget
public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! The matching-capacity hypothesis follows from the residual lower bound,
the prescribed-position estimate, and explicit bad-edge and target budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_matching_capacity_from_linear_budgets
    (d:ℕ) (hd:0<d) (θ α b η z:ℝ) (hθ:0<θ) (hα:0<α) (hb:0≤b)
    (hbudget:16/(d:ℝ)+16*η+16*b/α+4*z≤θ/8):
    ∃N:ℕ,∀(n:ℕ),N≤n→0<n→∀(R A:Finset (Fin n)) (G:SimpleGraph (Fin n)) (Z:Finset (Fin n)),
      (θ*n/4≤(R.card:ℝ))→
      ((residualSubtypeSet R A).card:ℝ)≤2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*η*n→
      (∀v,(G.degree v:ℝ)≤b*n)→(Z.card:ℝ)≤z*n→
      8*(residualSubtypeSet R A).card+8*⌈4*(G.edgeFinset.card:ℝ)/(α*Fintype.card (Fin n))⌉₊+4*Z.card+10≤Fintype.card {x // x∈R}:=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (θ*(d:ℝ)/256) (18*(d:ℝ)/32) (by positivity)
  refine ⟨N,?_⟩
  intro n hn hn0 R A G Z hrem hpres hdegree hZ
  have hnR:0≤(n:ℝ):=by positivity
  have hceil:=residual_matching_ceiling_bound hn0 G α b hα hb hdegree
  have hsmall:=hN n hn
  have hsmall':32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)+18≤θ*n/8:=by
    have hh:=mul_le_mul_of_nonneg_left hsmall (show 0≤32/(d:ℝ) by positivity)
    have heq1:(32/(d:ℝ))*((n:ℝ)^(3/4:ℝ)+18*(d:ℝ)/32)=32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)+18:=by field_simp <;> ring
    have heq2:(32/(d:ℝ))*(θ*(d:ℝ)/256*(n:ℝ))=θ*n/8:=by field_simp <;> ring
    nlinarith [heq1,heq2]
  have hbudgetN:=mul_le_mul_of_nonneg_right hbudget hnR
  have hfinal:((8*(residualSubtypeSet R A).card+8*⌈4*(G.edgeFinset.card:ℝ)/(α*Fintype.card (Fin n))⌉₊+4*Z.card+10:ℕ):ℝ)≤(R.card:ℝ):=by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring_nf at hpres hceil hsmall' hbudgetN ⊢
    linarith
  have hfinalN:(8*(residualSubtypeSet R A).card+8*⌈4*(G.edgeFinset.card:ℝ)/(α*Fintype.card (Fin n))⌉₊+4*Z.card+10:ℕ)≤R.card:=by exact_mod_cast hfinal
  simpa only [Fintype.card_coe] using hfinalN
end Oberwolfach
