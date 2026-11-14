module

public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.OrdinaryInducedParentThreshold

@[expose] public section
/-! The original inner parent-density margin gives fixed positive fractional
    weights for cycles of any permitted reserved length, before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_weights_general_from_parent_density
    (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃ c C:ℝ,0<c ∧ 0<C ∧ ∃N:ℕ,0<N ∧
      ∀(V:Type) [Fintype V] [DecidableEq V] (A:Finset V),N≤A.card→
      ∀(P:SimpleGraph V) (density:ℝ),cycleThreshold (m+1)+α≤density→
        (∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ))→
      ∃ weight:OrdinaryCycle (P.induce (A:Set V)) (m+1)→ℝ,
        (∀C₀,c/(A.card:ℝ)^(m-1)≤weight C₀ ∧ weight C₀≤C/(A.card:ℝ)^(m-1)) ∧
        (∀x y,(∑C₀,if C₀.val.val.Adj x y then weight C₀ else 0)=
          if (P.induce (A:Set V)).Adj x y then 1 else 0):=by
  obtain ⟨c,C,hc,hC,N,hN,hweights⟩:=positive_ordinary_fractional_cycle_weights (m+1) (by omega) α hα
  refine ⟨c,C,hc,hC,N,hN,?_⟩
  intro V _ _ A hn P density hthreshold hmin
  have hcard:Fintype.card {x:V // x∈(A:Set V)}=A.card:=by simp
  have hdeg:∀v:{x:V // x∈(A:Set V)},
      (cycleThreshold (m+1)+α)*A.card≤(((P.induce (A:Set V)).degree v):ℝ):=by
    intro v
    have hh:=(mul_le_mul_of_nonneg_right hthreshold (by positivity:(0:ℝ)≤A.card)).trans (hmin v.val)
    rw [induced_degree_intersection P A v]
    simpa only [Finset.inter_comm] using hh
  obtain ⟨weight,hw,he⟩:=hweights {x:V // x∈(A:Set V)} (by simpa only [hcard] using hn)
    (P.induce (A:Set V)) (by
      intro v
      have hh:=hdeg v
      rw [←hcard] at hh
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  refine ⟨weight,?_,?_⟩
  · intro C₀
    simpa only [show m+1-2=m-1 by omega,hcard] using hw C₀
  · exact ordinary_cycle_incidence_load_adjacency _ (m+1) weight he
end Oberwolfach
