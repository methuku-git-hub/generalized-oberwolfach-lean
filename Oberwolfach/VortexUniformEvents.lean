module

public import Oberwolfach.VortexCommonEvents
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! A uniform terminal-size threshold controls exponentially unlikely
failures at every vortex level, even though the number of levels grows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_exponential_common_event (C c ε χ : ℝ) (K : ℕ)
    (hc : 0<c) (hε : 0<ε) (hε1 : ε<1) (hχ : 0<χ) :
    ∃ M : ℕ,1≤M ∧ ∀ (Ω : Type) [Fintype Ω] (μ : FiniteLaw Ω)
      (n : ℕ→ℕ) (k : ℕ),
      (∀ i≤k,M≤n i) →
      (∀ i<k,(n (i+1):ℝ)≤ε*n i) →
      ∀ Good : ℕ→Ω→Prop,
      (∀ i≤k,1-C*(n i:ℝ)^K*Real.exp (-c*n i)≤μ.probability (Good i)) →
      1-χ≤μ.probability (fun ω=>∀ i≤k,Good i ω) := by
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow C K hc (p:=1) (by norm_num) 1
  let M := max 1 (max N (Nat.ceil (1/(χ*(1-ε)))))
  refine ⟨M,le_max_left _ _,?_⟩
  intro Ω _ μ n k hn hstep Good hGood
  have hMnat : 1≤M := le_max_left _ _
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hnn (i : ℕ) (hi : i≤k) : (0:ℝ)<n i := by exact_mod_cast (show 0<n i by have := hn i hi;omega)
  have hsum := vortex_fixed_domain_common_event μ ε M hε hε1 hM (fun i=>(n i:ℝ)) k hnn hstep
    (by exact_mod_cast hn k (le_refl _)) Good (by
      intro i hi
      have hnN : N≤n i := by have := hn i hi;dsimp [M] at *;omega
      have htail := hN (n i) hnN
      simp only [Real.rpow_natCast,Real.rpow_one,pow_one] at htail
      linarith only [hGood i hi,htail])
  have hceil : 1/(χ*(1-ε))≤(M:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (1/(χ*(1-ε)))≤M by dsimp [M];omega))
  have hden : 0<χ*(1-ε) := by positivity
  have hh := (div_le_iff₀ hden).mp hceil
  have hbound : 1/((1-ε)*(M:ℝ))≤χ := by
    apply (div_le_iff₀ (by positivity : 0<(1-ε)*(M:ℝ))).mpr
    nlinarith only [hh]
  linarith only [hsum,hbound]

end Oberwolfach
