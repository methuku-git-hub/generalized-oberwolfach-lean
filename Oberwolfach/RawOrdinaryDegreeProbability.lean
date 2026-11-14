module

public import Oberwolfach.RawOrdinaryDegreeCounts
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! The spoke minimum degree holds uniformly over the supplied marginal arrays,
with the same event for all ambient vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawWheelSpokeDegrees_uniform_probability
    (pstar ω : ℝ) (hpstar : 0<pstar) (hω : 0<ω) (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
      Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V) (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ v : V,(pstar*ω/2)*Fintype.card V≤
          (Fintype.card {u : U // rawWheelSpokes π d σ j v u}:ℝ)) := by
  let ε : ℝ := pstar*ω/2
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨N,hN⟩ := linear_deviation_failure_eventually_small 1 ((4*(d:ℝ)+3)^2) ε
    (by positivity) hε 1 q₀
  refine ⟨max N 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hlo hhi π ρ hρ hρ1 q hq hQ s hs hS j hnoshort pH hpH hj
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := (mul_pos hω hn0).trans_le hlo
  have hm : 0<Fintype.card U := by exact_mod_cast hm0
  have hh := rawWheelSpokeDegrees_event π ρ hρ hρ1 d hd q hq hQ s hs hS
    hnoshort hm j pH hj (ε*n) (by positivity)
  have htail := hN n (by dsimp [n] at *;omega) n ((4*(d:ℝ)+3)^2*Fintype.card U)
    hn0.le (by simp) (by positivity)
    (mul_le_mul_of_nonneg_left (show (Fintype.card U:ℝ)≤n by exact_mod_cast hhi) (by positivity))
  have hprob : 1-1/(n:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ v : V,|(Fintype.card {u : U // rawWheelSpokes π d σ j v u}:ℝ)-pH*Fintype.card U|<ε*n) := by
    dsimp only [n] at htail
    linarith
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ v
  have hh := (abs_lt.mp (hσ v)).1
  have h₁ := mul_le_mul_of_nonneg_right hpH (Nat.cast_nonneg (Fintype.card U) : (0:ℝ)≤Fintype.card U)
  have h₂ := mul_le_mul_of_nonneg_left hlo hpstar.le
  dsimp only [ε,n] at hh
  nlinarith only [hh,h₁,h₂]

end Oberwolfach
