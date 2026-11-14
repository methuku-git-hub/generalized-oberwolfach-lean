module

public import Oberwolfach.CycleHypergraphMatchingCardinality
public import Oberwolfach.ResourceRoundingTransfer

@[expose] public section
/-! A near-regular vertex-based cycle hypergraph has a matching covering
almost all vertices once the stated degree and codegree estimates hold. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_hypergraph_near_perfect
    (k B:ℕ) (hk:2≤k) (K a γ ε:ℝ) (hK:0<K) (ha:0<a)
    (hγ:0<γ) (hγ1:γ≤1) (hε:0≤ε) (hmargin:a*k≤1-ε):
    ∃ n₀:ℕ,∀ n D:ℕ,n₀≤n→n≤D→D≤n^B→
    ∀ (V E:Type) [Fintype V] [Fintype E] [DecidableEq V],
    ∀ (R:E→Finset V),
    n≤Fintype.card V→Fintype.card V≤n^B→
    (∀ e,(R e).card=k)→
    (∀ v,(1-ε)*D≤(Fintype.card (HypergraphEdgesAt R v):ℝ) ∧
      Fintype.card (HypergraphEdgesAt R v)≤D)→
    (∀ v z,v≠z→((Finset.univ.filter (fun e=>v∈R e ∧ z∈R e)).card:ℝ)≤K*D/n)→
    ∃ M:Finset E,(∀ e∈M,∀ f∈M,e≠f→Disjoint (R e) (R f)) ∧
      (1-γ)*(1-ε)*Fintype.card V≤(k:ℝ)*M.card := by
  obtain ⟨N,hN⟩:=cycle_hypergraph_matching_cardinality k B hk K a γ hK ha hγ
  refine ⟨max N 1,?_⟩
  intro n D hn hnD hDB V E _ _ _ R hnV hV hsize hdegrees hcodeg
  have hnpos:0<n:=by omega
  have hDpos:(0:ℝ)<D:=by exact_mod_cast (lt_of_lt_of_le hnpos hnD)
  have hkpos:(0:ℝ)<k:=by exact_mod_cast (show 0<k by omega)
  have hmarginpos:0<1-ε:=(mul_pos ha hkpos).trans_le hmargin
  have hpositive:∀ v,0<Fintype.card (HypergraphEdgesAt R v):=by
    intro v
    have hh: (0:ℝ)<Fintype.card (HypergraphEdgesAt R v):=
      (mul_pos hmarginpos hDpos).trans_le (hdegrees v).1
    exact_mod_cast hh
  have hsum: (1-ε)*(D:ℝ)*Fintype.card V≤(k:ℝ)*Fintype.card E:=by
    have hh:=(resource_set_sum_bounds R Finset.univ ((1-ε)*(D:ℝ)) D
      (fun v=>⟨(hdegrees v).1,by exact_mod_cast (hdegrees v).2⟩)).1
    simpa only [Finset.card_univ,Finset.inter_univ,hsize,Finset.sum_const,
      nsmul_eq_mul,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using hh
  have hnV':(n:ℝ)≤Fintype.card V:=by exact_mod_cast hnV
  have hE: a*D*n≤(Fintype.card E:ℝ):=by
    have h1:=mul_le_mul_of_nonneg_right hmargin (mul_nonneg hDpos.le (Nat.cast_nonneg (Fintype.card V)))
    have h2:=mul_le_mul_of_nonneg_left hnV' (mul_nonneg ha.le hDpos.le)
    have hh:=mul_le_mul_of_nonneg_right h2 hkpos.le
    nlinarith
  obtain ⟨M,hM,hcard⟩:=hN n D ((le_max_left N 1).trans hn) hnD hDB V E R hV hsize hpositive
    (fun v=>(hdegrees v).2) hcodeg hE
  refine ⟨M,hM,?_⟩
  have hscale:=mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hγ1)
  have hmatch:=mul_le_mul_of_nonneg_left hcard hkpos.le
  have hmatch':(1-γ)*(k:ℝ)*Fintype.card E≤(k:ℝ)*(M.card:ℝ)*D:=by
    have h:=mul_le_mul_of_nonneg_right hmatch hDpos.le
    field_simp at h
    nlinarith
  have hfinal: ((1-γ)*(1-ε)*Fintype.card V)*D≤((k:ℝ)*M.card)*D:=by nlinarith
  exact le_of_mul_le_mul_right hfinal hDpos
end Oberwolfach
