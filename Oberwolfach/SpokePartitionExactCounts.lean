module

public import Oberwolfach.MarkedOccurrenceDegreesDivisible

@[expose] public section
/-! The retained marked spokes partition each residual spoke set, and their
exact sizes give the hub divisibility identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem spoke_partition_exact_counts
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (R Y:U→Finset V) (m:ℕ) (hYR:∀u,Y u⊆R u)
    (hsize:∀u,(R u).card=(m+1)*(Y u).card):
    (∀v,(∑u,if v∈R u\Y u then (1:ℝ) else 0)+
      (∑u,if v∈Y u then (1:ℝ) else 0)=(∑u,if v∈R u then (1:ℝ) else 0)) ∧
    (∀u,(∑v,if v∈R u\Y u then (1:ℝ) else 0)=
      (m:ℝ)*(∑v,if v∈Y u then (1:ℝ) else 0)):=by
  constructor
  · intro v
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hy:v∈Y u
    · have hr:=hYR u hy
      simp [hy,hr]
    · simp [hy]
  · intro u
    rw [Finset.sum_boole,Finset.sum_boole]
    have h1:(Finset.univ.filter (fun v=>v∈R u\Y u))=R u\Y u:=by ext v; simp
    have h2:(Finset.univ.filter (fun v=>v∈Y u))=Y u:=by ext v; simp
    rw [h1,h2]
    have hc:=Finset.card_sdiff_add_card_eq_card (hYR u)
    have hs:=hsize u
    have hn:(R u\Y u).card=m*(Y u).card:=by nlinarith
    exact_mod_cast hn
end Oberwolfach
