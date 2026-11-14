module

public import Oberwolfach.OrdinaryDeepCoverNamedEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_named_deep_cover_high_probability (m:ℕ) (hm:3≤m) (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ K:ℕ,0<K ∧ ∃ a ε₀ ρ θ:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θ ∧
    ∀ Dmax d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (J:Finset U),N≤Fintype.card V →
      (J.card:ℝ)≤a*Fintype.card V →
      ω*Fintype.card V≤((Finset.univ\J).card:ℝ) → Fintype.card U≤Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,F.degree v≤Dmax) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (OrdinaryDeepCoverEvent m K a ρ θ P F J π d j) :=by
  obtain ⟨K,hK,a,ε₀,ρ,θ,ha,hε₀,hρ,hθ,hmain⟩:=ordinary_deep_cover_finite_sets_common_event m hm α p ω hα hp hp1 hω
  refine ⟨K,hK,a,ε₀,ρ,θ,ha,hε₀,hρ,hθ,?_⟩
  intro Dmax d q₀ hd
  obtain ⟨N,hN⟩:=hmain Dmax d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π J hn hJ hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hh:=hN V U Γ Color P F π J hn hJ hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  unfold OrdinaryDeepCoverEvent
  exact hσ
end Oberwolfach
