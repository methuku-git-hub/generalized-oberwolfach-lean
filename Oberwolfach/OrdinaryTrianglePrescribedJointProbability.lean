module

public import Oberwolfach.OrdinaryHubTriangleJointProbability
public import Oberwolfach.OrdinaryPrescribedInnerNamed

@[expose] public section
/-! Prescribed-edge, hub-cover, and triangle row-cover events share one
original raw sample. Their individual constants retain their quantifier order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_prescribed_joint_probability (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ a₀ ε₀ ρhub η θ ρ:ℝ,0<a₀ ∧ 0<ε₀ ∧ 0<ρhub ∧ 0<η ∧ 0<θ ∧ 0<ρ ∧
    ∀ a:ℝ,0<a → a≤a₀ → ∀Dmax d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V) (B:Finset U),N≤Fintype.card V →
      ω*Fintype.card V≤(B.card:ℝ) → Fintype.card U≤Fintype.card V →
      (∀v,(cycleThreshold 3+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀v,F.degree v≤Dmax) → permutationConflictGraph π (3*d)≤F →
      (∀v k,0<k→k<2*d+1→(π^k) v≠v) →
    ∀(pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀(q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j:Color),(∀u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (fun σ=>OrdinaryPrescribedInnerEvent 3 P F π d a p (min α 1) Finset.univ Finset.univ j σ ∧
          OrdinaryHubCoverEvent 2 P F π d ρhub j σ ∧
          OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ B pR pH η θ ρ j σ):=by
  obtain ⟨ε₀,ρhub,η,θ,ρ,hε,hρhub,hη,hθ,hρ,hjoint⟩:=ordinary_hub_triangle_events_joint_high_probability α p ω hα hp hp1 hω
  let γ:=min α 1
  have hγ:0<γ:=lt_min hα zero_lt_one
  obtain ⟨a₀,ha₀,ha₀one,hpre⟩:=prescribed_inner_packing_common_event 3 (by omega) p γ ω 1 hp hp1 hγ (min_le_right _ _) hω le_rfl
  refine ⟨a₀,ε₀,ρhub,η,θ,ρ,ha₀,hε,hρhub,hη,hθ,hρ,?_⟩
  intro a ha ha₀' Dmax d q₀ hd
  obtain ⟨Nj,hj⟩:=hjoint Dmax d (q₀+1) hd
  obtain ⟨Np,hp'⟩:=hpre a Dmax ha ha₀' (Nat.cast_nonneg _) d (q₀+1) hd
  refine ⟨max 2 (max Nj Np),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π B hn hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hjp
  have hnN:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnN
  have hUlo:ω*Fintype.card V≤(Fintype.card U:ℝ):=hB.trans (Nat.cast_le.mpr (Finset.card_le_univ B))
  have hPpre (v:V):(1/2+γ)*(Finset.univ:Finset V).card≤((Finset.univ∩P.neighborFinset v).card:ℝ):=by
    have hh:(1/2:ℝ)+γ≤cycleThreshold 3+α:=by
      have hhalf:=cycleThreshold_half_le (show 3≤3 by omega)
      have hga:=min_le_left α 1
      dsimp [γ];linarith only [hhalf,hga]
    simpa only [Finset.card_univ,Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using
      (mul_le_mul_of_nonneg_right hh hnR.le).trans (hP v)
  have hA:=hj V U Γ Color P F π B (by omega) hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hjp
  have hBpre:=hp' V U Γ Color P F π Finset.univ Finset.univ
    (by simpa using (show Np≤Fintype.card V by omega))
    (by simp) (by simpa using (Nat.cast_le.mpr hU:(Fintype.card U:ℝ)≤Fintype.card V))
    (by simpa using hUlo) hclose (fun v=>Nat.cast_le.mpr (hF v)) hPpre hnoshort
    pR pH (hp.le.trans hpR) hpR1 hpR hpH q hq hQ s hs hS j hjp
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)
  have hpreprob:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability
      (OrdinaryPrescribedInnerEvent 3 P F π d a p γ Finset.univ Finset.univ j):=by
    simp only [Finset.card_univ] at hBpre
    apply hBpre.trans
    apply finiteLaw_probability_mono
    intro σ hs
    unfold OrdinaryPrescribedInnerEvent
    simp only [Finset.card_univ]
    convert hs using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
  have hjointprob:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability
      (fun σ=>OrdinaryHubCoverEvent 2 P F π d ρhub j σ ∧
        OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ B pR pH η θ ρ j σ):=hA
  have hi:=finiteLaw_good_intersection μ (OrdinaryPrescribedInnerEvent 3 P F π d a p γ Finset.univ Finset.univ j)
    (fun σ=>OrdinaryHubCoverEvent 2 P F π d ρhub j σ ∧
      OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ B pR pH η θ ρ j σ)
    (1/(Fintype.card V:ℝ)^(q₀+1)) hjointprob
  have hb:=scaled_inverse_power_le (Fintype.card V) q₀ hnN 2 (by exact_mod_cast (show 2≤Fintype.card V by omega))
  have hb':2*(1/(Fintype.card V:ℝ)^(q₀+1))≤1/(Fintype.card V:ℝ)^q₀:=by convert hb using 1 <;> ring
  dsimp [γ] at hpreprob hi
  linarith only [hi,hpreprob,hb']
end Oberwolfach
