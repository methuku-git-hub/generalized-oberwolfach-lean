module

public import Oberwolfach.UniformWeightedHypergraphMatching

@[expose] public section
/-! The weighted matching theorem applied to a cycle hypergraph with its
vertices taken to be the vertices of the underlying graph. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_hypergraph_matching_cardinality
    (k B:ℕ) (hk:2≤k) (K a γ:ℝ) (hK:0<K) (ha:0<a) (hγ:0<γ):
    ∃ n₀:ℕ,∀ n D:ℕ,n₀≤n→n≤D→D≤n^B→
    ∀ (V E:Type) [Fintype V] [Fintype E] [DecidableEq V],
    ∀ (R:E→Finset V),
    Fintype.card V≤n^B→
    (∀ e,(R e).card=k)→(∀ v,0<Fintype.card (HypergraphEdgesAt R v))→
    (∀ v,Fintype.card (HypergraphEdgesAt R v)≤D)→
    (∀ v z,v≠z→((Finset.univ.filter (fun e=>v∈R e ∧ z∈R e)).card:ℝ)≤K*D/n)→
    a*D*n≤(Fintype.card E:ℝ)→
    ∃ M:Finset E,(∀ e∈M,∀ f∈M,e≠f→Disjoint (R e) (R f)) ∧
      (1-γ)*(Fintype.card E:ℝ)/D≤M.card := by
  obtain ⟨N,hN⟩:=uniform_weighted_hypergraph_matching k B hk K a γ hK ha hγ
  refine ⟨max N 1,?_⟩
  intro n D hn hnD hDB V E _ _ _ R hV hsize hpositive hdegree hcodeg htotal
  have hnpos:0<n:=by omega
  have hpow:1≤n^B:=Nat.succ_le_iff.mpr (pow_pos hnpos B)
  obtain ⟨M,hM,hweight⟩:=hN n D ((le_max_left N 1).trans hn) hnD hDB V E Unit R
    (fun _ _=>1) (fun _=>1) (fun _=>(Fintype.card E:ℝ)) hV (by simpa using hpow)
    hsize hpositive hdegree hcodeg (by intro;norm_num) (by intro;norm_num)
    (by intro; simp) (by intro;simpa using htotal)
  refine ⟨M,hM,?_⟩
  have h:=hweight ()
  simp only [Finset.sum_const_zero,Finset.sum_const,Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hlo:-(γ*(Fintype.card E:ℝ)/D)<(M.card:ℝ)-(Fintype.card E:ℝ)/D:=(abs_lt.mp h).1
  have hDpos:(0:ℝ)<D:=by exact_mod_cast (lt_of_lt_of_le hnpos hnD)
  have hdiv:((1-γ)*(Fintype.card E:ℝ)/D)=
     (Fintype.card E:ℝ)/D-γ*(Fintype.card E:ℝ)/D:=by ring
  rw [hdiv];linarith
end Oberwolfach
