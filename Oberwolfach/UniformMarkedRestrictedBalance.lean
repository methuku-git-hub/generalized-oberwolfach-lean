module

public import Oberwolfach.RawMarkedRestrictedBalance
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! Uniform restricted balance at a supplied local scale. Constants and
order thresholds precede the domains, host, actual marginals and exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedRestrictedBalanceExponent (m d : ℕ) (η K : ℝ) : ℝ :=
  2*(η/(4*((m:ℝ)+4)))^2/((4*(d:ℝ)+3)^2*K)

theorem markedRestrictedBalanceExponent_pos (m d : ℕ) (η K : ℝ) (hη : 0<η) (hK : 0<K) :
    0<markedRestrictedBalanceExponent m d η K := by unfold markedRestrictedBalanceExponent;positivity

theorem marked_restricted_balance_uniform_event (m d : ℕ) (hd : 2≤d) (η K : ℝ) (hη : 0<η) (hK : 1≤K) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    ∀ M : ℕ,N≤M → (Fintype.card V:ℝ)≤K*M → (Fintype.card U:ℝ)≤K*M →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (A : Finset V) (B : Finset U),
      A.Nonempty → B.Nonempty → A.card≤M → B.card≤M → (∀ x,π x∈A ↔ x∈A) →
    ∀ D δP : ℝ,0≤δP → δP≤η/4 → (∀ x,|((P.neighborFinset x∩A).card:ℝ)-D|≤δP*M) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) →
      p*D=s₀*B.card → k*D=t₀*B.card → s₀=(m:ℝ)*t₀ →
    1-16*K*M*Real.exp (-markedRestrictedBalanceExponent m d η K*M)≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
        (RawMarkedRestrictedBalance P π d m g j A B (η*M)) := by
  let ε := η/(4*((m:ℝ)+4))
  have hε : 0<ε := by dsimp [ε];positivity
  have hK0 : 0<K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨N,hN⟩ := exists_nat_ge (8*(6*(d:ℝ)+1)/η)
  refine ⟨max 1 N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ M hMN hV hU P π A B hA hB hAM hBM hInv D δP hδP hδη hP p k hp hk hsum q hq hQ s hs hS hnoshort g j s₀ t₀ hg hj hD0 hDK hratio
  have hM : 0<M := by omega
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  have hAR : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
  have hBR : (0:ℝ)<B.card := by exact_mod_cast hB.card_pos
  have hVR : (0:ℝ)<Fintype.card V := by exact_mod_cast hA.card_pos.trans_le A.card_le_univ
  have hAMR : (A.card:ℝ)≤M := by exact_mod_cast hAM
  have hBMR : (B.card:ℝ)≤M := by exact_mod_cast hBM
  have hnR : (N:ℝ)≤M := by exact_mod_cast (show N≤M by omega)
  have hmargin := (div_le_iff₀ hη).mp (hN.trans hnR)
  have heps : ((m:ℝ)+4)*ε=η/4 := by dsimp [ε];field_simp
  have hδM := mul_le_mul_of_nonneg_right hδη hMR.le
  have herror : ((m:ℝ)+4)*(ε*M)+2*(6*(d:ℝ)+1)+δP*M≤η*M := by
    rw [← mul_assoc,heps]
    nlinarith only [hmargin,hδM,mul_pos hη hMR]
  have hh := rawMarked_restricted_balance_event P π d m hd A B hA hB hInv D (δP*M) (ε*M)
    (by positivity) (by positivity) hP p k hp hk hsum q hq hQ s hs hS hnoshort g j s₀ t₀ hg hj hD0 hDK hratio
  let H := (4*(d:ℝ)+3)^2*K
  have hH : 0<H := by dsimp [H];positivity
  have hH1 : 1≤H := by
    have hsq : 1≤(4*(d:ℝ)+3)^2 := by nlinarith [show (0:ℝ)≤d from Nat.cast_nonneg d]
    exact (show (1:ℝ)=1*1 by ring).le.trans (mul_le_mul hsq hK (by norm_num) (by positivity))
  have hDA : (A.card:ℝ)≤H*M := hAMR.trans (by nlinarith only [hH1,mul_nonneg (sub_nonneg.mpr hH1) hMR.le])
  have hDB : (4*(d:ℝ)+3)^2*B.card≤H*M := by
    dsimp [H]
    have hbK : (B.card:ℝ)≤K*M := hBMR.trans (by nlinarith only [hK,hMR])
    nlinarith only [mul_le_mul_of_nonneg_left hbK (sq_nonneg (4*(d:ℝ)+3))]
  have hDV : (4*(d:ℝ)+3)^2*Fintype.card V≤H*M := by dsimp [H];nlinarith only [mul_le_mul_of_nonneg_left hV (sq_nonneg (4*(d:ℝ)+3))]
  have hR := linear_deviation_failure_exponential (4*K) H ε hH hε 1 M hM
    (4*Fintype.card V) A.card (by positivity) (by simp only [pow_one];nlinarith only [hV]) hAR hDA
  have hRow := linear_deviation_failure_exponential (2*K) H ε hH hε 1 M hM
    (2*Fintype.card V) ((4*(d:ℝ)+3)^2*B.card) (by positivity)
    (by simp only [pow_one];nlinarith only [hV]) (by positivity) hDB
  have hCol := linear_deviation_failure_exponential (2*K) H ε hH hε 1 M hM
    (2*Fintype.card U) ((4*(d:ℝ)+3)^2*Fintype.card V) (by positivity)
    (by simp only [pow_one];nlinarith only [hU]) (by positivity) hDV
  simp only [pow_one] at hR hRow hCol
  have hbound : 1-16*K*M*Real.exp (-markedRestrictedBalanceExponent m d η K*M)≤
      1-8*Fintype.card V*Real.exp (-2*(ε*M)^2/A.card)-
        4*Fintype.card V*Real.exp (-2*(ε*M)^2/((4*(d:ℝ)+3)^2*B.card))-
        4*Fintype.card U*Real.exp (-2*(ε*M)^2/((4*(d:ℝ)+3)^2*Fintype.card V)) := by
    change 1-16*K*M*Real.exp (-(2*ε^2/H)*M)≤_
    nlinarith only [hR,hRow,hCol]
  apply (hbound.trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨?_,?_⟩
  · intro x
    exact ⟨fun incoming=>(hσ.1 x).1 incoming |>.trans herror,((hσ.1 x).2).trans herror⟩
  · intro u
    exact (hσ.2 u).trans herror

end Oberwolfach
