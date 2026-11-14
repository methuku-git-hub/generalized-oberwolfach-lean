module

public import Oberwolfach.OrdinaryHubCoverNamed

@[expose] public section
/-! The existing high-probability hub event in a named, composable form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_hub_cover_named_probability (m:ℕ) (hm:2≤m) (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ ε₀ ρ:ℝ,0<ε₀ ∧ 0<ρ ∧ ∀ Dmax:ℝ,0≤Dmax →
    ∀ d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ P:SimpleGraph V,N≤Fintype.card V →
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (F:SimpleGraph V) (π:Equiv.Perm V),(∀ v,(F.degree v:ℝ)≤Dmax) →
      permutationConflictGraph π (3*d)≤F → (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (OrdinaryHubCoverEvent m P F π d ρ j) :=by
  obtain ⟨ε₀,ρ,hε,hρ,h⟩:=ordinary_hub_cover_common_event m hm α p ω hα hp hp1 hω
  refine ⟨ε₀,ρ,hε,hρ,?_⟩
  intro Dmax hDmax d q₀ hd
  obtain ⟨N,hN⟩:=h Dmax hDmax d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P hn hUlo hU hP F π hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hh:=hN V U Γ Color P hn hUlo hU hP F π hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  convert hh using 1 <;> simp only [OrdinaryHubCoverEvent] <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
