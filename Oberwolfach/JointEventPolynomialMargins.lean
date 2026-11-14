module

public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.FiniteUniform

@[expose] public section
/-! Fixed error budgets and two inverse-power terms leave a positive
probability for one common outcome at a uniform large-order threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem joint_event_polynomial_margin
    (a A B q r:ℝ) (ha:a<1) (hq:0<q) (hr:0<r):
    ∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→a+A*(n:ℝ)^(-q)+B*(n:ℝ)^(-r)<1:=by
  have hlim1:=((tendsto_rpow_neg_atTop hq).const_mul A).comp tendsto_natCast_atTop_atTop
  have hlim2:=((tendsto_rpow_neg_atTop hr).const_mul B).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlim1 hlim2
  have hlim:=hlim1.add hlim2
  simp only [zero_add] at hlim
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (show (0:ℝ)<1-a by linarith)))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn
  have hh:=hN n (by omega)
  dsimp only [Function.comp_apply] at hh
  linarith

theorem joint_event_positive_mass_witness
    (a A B q r:ℝ) (ha:a<1) (hq:0<q) (hr:0<r):
    ∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→∀ {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop),
      1-a-A*(n:ℝ)^(-q)-B*(n:ℝ)^(-r)≤μ.probability E→
      ∃ ω,E ω ∧ 0<μ.mass ω:=by
  obtain ⟨N,hN,hmargin⟩:=joint_event_polynomial_margin a A B q r ha hq hr
  refine ⟨N,hN,?_⟩
  intro n hn Ω _ μ E hE
  have hprob:0<μ.probability E:=by linarith [hmargin n hn]
  unfold FiniteLaw.probability at hprob
  have hnonneg:∀ ω∈(Finset.univ:Finset Ω),0≤(if E ω then μ.mass ω else 0):=by
    intro ω _
    split_ifs
    · exact μ.nonneg ω
    · norm_num
  obtain ⟨ω,_,hω⟩:=(Finset.sum_pos_iff_of_nonneg hnonneg).mp hprob
  by_cases h:E ω
  · exact ⟨ω,h,by simpa [h] using hω⟩
  · simp [h] at hω
end Oberwolfach
