module

public import Oberwolfach.OrdinaryHubCoverNamedProbability
public import Oberwolfach.OrdinaryTriangleTwoDomainHighProbability
public import Oberwolfach.TwoCommonEvents

@[expose] public section
/-! The robust hub-cover and triangle row-cover events occur on the same
original raw sample, with their probabilities combined before any edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_triangle_events_joint_high_probability (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ε₀ ρhub η θ ρ:ℝ,0<ε₀ ∧ 0<ρhub ∧ 0<η ∧ 0<θ ∧ 0<ρ ∧
    ∀Dmax d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V) (B:Finset U),N≤Fintype.card V →
      ω*Fintype.card V≤(B.card:ℝ) → Fintype.card U≤Fintype.card V →
      (∀v,(cycleThreshold 3+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀v,F.degree v≤Dmax) → permutationConflictGraph π (3*d)≤F →
      (∀v k,0<k→k<2*d+1→(π^k) v≠v) →
    ∀(pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀(q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀u a,0≤s u a)
      (hS:∀u,∑a,s u a≤ intervalUncoveredProbability d (∑a,q u a))
      (j:Color),(∀u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (fun σ=>OrdinaryHubCoverEvent 2 P F π d ρhub j σ ∧
          OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ B pR pH η θ ρ j σ):=by
  obtain ⟨ε₀,ρhub,hε,hρhub,hHub⟩:=ordinary_hub_cover_named_probability 2 (by omega) α p ω hα hp hp1 hω
  obtain ⟨η,θ,ρ,hη,hθ,hρ,hTri⟩:=ordinary_triangle_two_domain_rows_high_probability 2 ω p (by norm_num) hω hp hp1
  refine ⟨ε₀,ρhub,η,θ,ρ,hε,hρhub,hη,hθ,hρ,?_⟩
  intro Dmax d q₀ hd
  obtain ⟨Nh,hH⟩:=hHub Dmax (Nat.cast_nonneg _) d (q₀+1) hd
  obtain ⟨Nt,hT⟩:=hTri d (q₀+1) hd
  obtain ⟨Ns,hNs⟩:=exists_nat_gt (((2*d+1:ℕ):ℝ)/ω)
  refine ⟨max 2 (max Ns (max Nh Nt)),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π B hn hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hnN:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnN
  have hUlo:ω*Fintype.card V≤(Fintype.card U:ℝ):=hB.trans (Nat.cast_le.mpr (Finset.card_le_univ B))
  have hnsize:(Ns:ℝ)≤Fintype.card V:=by exact_mod_cast (show Ns≤Fintype.card V by omega)
  have hUsmall:(2*d+1:ℕ)≤Fintype.card U:=by
    have hh:((2*d+1:ℕ):ℝ)<ω*Ns:=by simpa only [mul_comm] using (div_lt_iff₀ hω).mp hNs
    have hm:=mul_le_mul_of_nonneg_left hnsize hω.le
    have hreal:((2*d+1:ℕ):ℝ)≤Fintype.card U:=by linarith
    exact_mod_cast hreal
  have hparent:∀x∈(Finset.univ:Finset V),∀v∈insert x Finset.univ,
      (3/4:ℝ)*(Finset.univ:Finset V).card≤((Finset.univ∩P.neighborFinset v).card:ℝ):=by
    intro x hx v hv
    have hc:(3/4:ℝ)≤cycleThreshold 3+α:=by linarith [cycleThreshold_triangle_lower]
    simpa only [Finset.card_univ,Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using
      (mul_le_mul_of_nonneg_right hc hnR.le).trans (hP v)
  have ph:=hH V U Γ Color P (by omega) hUlo hU hP F π (fun v=>Nat.cast_le.mpr (hF v)) hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have pt:=hT V U Γ Color P F π Finset.univ Finset.univ B Dmax
    (by simpa only [Finset.card_univ] using (show Nt≤Fintype.card V by omega))
    (by simp only [Finset.card_univ];have hh:((Fintype.card U:ℝ)≤Fintype.card V):=Nat.cast_le.mpr hU;linarith)
    (by simpa only [Finset.card_univ] using hB)
    (by simpa only [Finset.card_univ] using (Finset.card_le_univ B |>.trans hU)) hUsmall hparent hclose hF hnoshort
    pR pH hpR hpR1 hpH hpH1 q hq hQ s hs hS j hj
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)
  have hb:=scaled_inverse_power_le (Fintype.card V) q₀ hnN 2 (by exact_mod_cast (show 2≤Fintype.card V by omega))
  have hb':2*(1/(Fintype.card V:ℝ)^(q₀+1))≤1/(Fintype.card V:ℝ)^q₀:=by convert hb using 1 <;> ring
  have hpt:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability
      (OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ B pR pH η θ ρ j):=by
    simpa only [Finset.card_univ] using pt
  have hhi:=finiteLaw_good_intersection μ (OrdinaryHubCoverEvent 2 P F π d ρhub j)
    (OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ B pR pH η θ ρ j)
    (1/(Fintype.card V:ℝ)^(q₀+1)) hpt
  have hph:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability (OrdinaryHubCoverEvent 2 P F π d ρhub j):=ph
  linarith only [hhi,hph,hb']
end Oberwolfach
