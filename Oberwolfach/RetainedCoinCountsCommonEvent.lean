module

public import Oberwolfach.EdgeRetention
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! Simultaneous counts for fixed sets of physical coins. A coordinate is
sampled once even when it belongs to several sets. The order threshold is
uniform over the retention probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_coin_count_tail {E:Type} [Fintype E] [DecidableEq E]
    (A:Finset E) (p:ℝ) (hp:0≤p) (hp1:p≤1) (n t:ℝ) (hA:(A.card:ℝ)≤n) (ht:0≤t):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>t≤|((A.filter (fun e=>σ e=true)).card:ℝ)-p*A.card|)≤2*Real.exp (-2*t^2/n):=by
  have hh:=finiteLaw_singleton_patterns_tail_at_scale
    (fun _:E=>FiniteLaw.retentionCoin p hp hp1) A id (fun _ _=>true)
    (fun _ _ _ _ h=>h) hA ht
  have hid (σ:E→Bool):(∑ e∈A,patternValue {id e} (fun _=>true) σ)=
      ((A.filter (fun e=>σ e=true)).card:ℝ):=by
    simp only [patternValue,Finset.prod_singleton,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,id_eq]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he:σ e=true <;> simp only [he,ite_true,ite_false]
  have hm:(∑ i∈A,(FiniteLaw.retentionCoin p hp hp1).mass true)=p*A.card:=by
    simp only [FiniteLaw.retentionCoin,ite_true,Finset.sum_const,nsmul_eq_mul];ring
  simpa only [hid,hm] using hh

theorem retained_coin_counts_common_event (C M ε:ℝ) (hM:0<M) (hε:0<ε) (k q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (E J:Type) [Fintype E] [DecidableEq E] [Fintype J],
    (Fintype.card J:ℝ)≤C*(n:ℝ)^k→∀ A:J→Finset E,
    (∀ j,((A j).card:ℝ)≤M*n)→∀ (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(n:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ j,|(((A j).filter (fun e=>σ e=true)).card:ℝ)-p*(A j).card|<ε*n):=by
  obtain ⟨N,hN⟩:=linear_deviation_failure_eventually_small C M ε hM hε k q
  refine ⟨max 1 N,?_⟩
  intro n hn E J _ _ _ hJ A hA p hp hp1
  have hnR:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)
  let Bad:=fun j (σ:E→Bool)=>ε*n≤|(((A j).filter (fun e=>σ e=true)).card:ℝ)-p*(A j).card|
  let err:=2*Real.exp (-2*(ε*n)^2/(M*n))
  have hh:=finiteLaw_common_event_lower μ Finset.univ Bad (fun _=>err)
    (fun j _=>retained_coin_count_tail (A j) p hp hp1 (M*n) (ε*n) (hA j) (by positivity))
  have hsmall:=hN n (by omega) (Fintype.card J) (M*n) (Nat.cast_nonneg _) hJ (by positivity) le_rfl
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,Bad,not_le] at hh
  exact (sub_le_sub_left hsmall 1).trans hh
end Oberwolfach
