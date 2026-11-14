module

public import Oberwolfach.RawMarkedHubCounts
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! Uniform compatible-hub lower bounds, before actual feasible arrays
are supplied. Every separated tuple is controlled on one raw-law event;
its physical rim edges may be absent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarkedHubs_exponential_probability
    (m : ℕ) (sstar tstar ω : ℝ) (hsstar : 0<sstar) (htstar : 0<tstar) (hω : 0<ω) :
    ∀ d : ℕ,∀ hd : 2≤d,
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      0<Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color),(∀ u,tstar≤q u g) → (∀ u,sstar≤s u j) →
      (∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    1-2*(Fintype.card V:ℝ)^(m+1)*Real.exp
      (-(2*(ω*tstar*sstar^m/2)^2/((4*(d:ℝ)+3)^2*((m:ℝ)+1)))*Fintype.card V)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
          (ω*tstar*sstar^m/2)*Fintype.card V≤((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)) := by
  let β : ℝ := ω*tstar*sstar^m/2
  have hβ : 0<β := by dsimp [β];positivity
  intro d hd
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi π q hq hQ s hs hS g j hg hj hnoshort
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<Fintype.card U := by exact_mod_cast hm0
  have hh := rawMarkedHubs_common_event π d hd q hq hQ s hs hS hnoshort hm m g j (β*n) (by positivity)
  have hM : (Fintype.card U:ℝ)≤n := by exact_mod_cast hmhi
  have ht := linear_deviation_failure_exponential 1 ((4*(d:ℝ)+3)^2*((m:ℝ)+1))
    β (by positivity) hβ (m+1) n hn ((n:ℝ)^(m+1))
    ((4*(d:ℝ)+3)^2*(((m:ℝ)+1)*Fintype.card U))
    (by positivity) (by simp) (by positivity) (by
      have hmul := mul_le_mul_of_nonneg_left hM
        (show 0≤(4*(d:ℝ)+3)^2*((m:ℝ)+1) by positivity)
      nlinarith only [hmul])
  norm_num only [mul_one] at ht
  have hprob := (sub_le_sub_left ht 1).trans hh
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ C hC
  have hcount := (abs_lt.mp (hσ C hC)).1
  have hmean : (Fintype.card U:ℝ)*(tstar*sstar^m)≤∑ u : U,q u g*(s u j)^m := by
    rw [← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
    apply Finset.sum_le_sum
    intro u _
    exact mul_le_mul (hg u) (by gcongr;exact hj u) (by positivity) (hq u g)
  have hmean' := mul_le_mul_of_nonneg_right hmlo (show 0≤tstar*sstar^m by positivity)
  dsimp only [β] at hcount ⊢
  nlinarith only [hcount,hmean,hmean']

end Oberwolfach
