module

public import Oberwolfach.OrdinaryBoundedNeighbourhoodEvent
public import Oberwolfach.OrdinaryJointProbabilityMargin

@[expose] public section
/-! The actual bounded-order row and index event has enough probability to
intersect the sampled profile event on the same law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_preparation_probability_exceeds_profile_failure (ω ε:ℝ) (hω:0<ω) (hε:0<ε)
    (d h:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V), permutationConflictGraph π (3*d)≤F →
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ (p:ℝ) (hp:0≤p) (hp1:p≤1)
      (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color) (pH:ℝ),(∀ u,s u j=pH) →
    2/(Fintype.card V:ℝ)^2 <
      (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
        (fun σ=>RawOrdinaryRows P π d h Finset.univ p s j (ε*Fintype.card V) σ ∧
          RawOrdinaryIndices F π d h pH j (ε*Fintype.card U) σ) := by
  obtain ⟨N,hN⟩:=ordinary_bounded_neighbourhood_common_event 1 ω ε (by norm_num) hω hε d 1 h hd
  refine ⟨max 4 N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort p hp hp1 q hq hQ s hs hS j pH hj
  have hprob:=hN V U Γ Color P F π Finset.univ (by simpa using (show N≤Fintype.card V by omega))
    (by simp) (by simpa using (Nat.cast_le.mpr hu : (Fintype.card U:ℝ)≤Fintype.card V))
    (by simpa using hlo) hF hnoshort p hp hp1 q hq hQ s hs hS j pH hj
  simp only [Finset.card_univ, pow_one] at hprob
  exact ordinary_joint_probability_margin (Fintype.card V) (by omega) _ hprob
end Oberwolfach
