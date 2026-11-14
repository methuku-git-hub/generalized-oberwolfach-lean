module

public import Oberwolfach.ThinnedCommonClassGeometry

@[expose] public section

/-! Accurate class sizes are preserved in addition to the density needed
for greedy counts. Both estimates concern the very same vertex coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem thinnedCommonClass_size_event (ε : ℝ) (hε : 0<ε) (d Q : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ∀ (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U),u≠u' →
    1-1/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
        (fun σ=>∀ b,|((thinnedCommonClass π d g j u u' σ b).card:ℝ)-
          (if b then q u g*q u' g else s u j*s u' j*θ)*Fintype.card V|≤ε*Fintype.card V) := by
  obtain ⟨N,hN⟩ := linear_deviation_failure_eventually_small 2 ((16*(d:ℝ)+14)^2) ε (by positivity) hε 0 Q
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN π hnoshort p k hp hk hphys q hq hQ s hs hS θ hθ hθ1 g j u u' hu
  have hn : 0<Fintype.card V := by omega
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hh := thinnedCommonClassCount_common_event π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
    θ hθ hθ1 g j u u' hu (fun _ : Unit=>Finset.univ) hn (ε*Fintype.card V) (by positivity)
  simp only [Fintype.card_unique,Nat.cast_one,mul_one] at hh
  have ht := hN (Fintype.card V) (by omega) 2 ((16*(d:ℝ)+14)^2*Fintype.card V)
    (by norm_num) (by simp) (by positivity) le_rfl
  apply ((sub_le_sub_left ht 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ b
  have hc := (hσ b ()).le
  simpa only [thinnedCommonClassCount_card,Finset.card_univ,thinnedCommonClass] using hc

end Oberwolfach
