module

public import Oberwolfach.RawOrdinaryTransferUniformEvent
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! A uniform polynomial failure bound for all potential transfers in the
original raw sample. The configuration constant precedes the interval length,
conflict degree, host, and all marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_ordinary_transfer_uniform_probability
    (r : ℕ) (hr : 3≤r) (α pstar : ℝ) (hα : 0<α) (hpstar : 0<pstar) (hpstar1 : pstar≤1)
    (hδ : (if r=3 then (3/4:ℝ) else 1/2)+α/2≤1) :
    ∃ b : ℝ,0<b ∧ ∀ (L : ℝ),0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d, ∃ N : ℕ,
    ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V →
      Fintype.card U≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (π : Equiv.Perm V),
    (∀ v,((if r=3 then (3/4:ℝ) else 1/2)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    ∀ (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1),
      (∀ e∈P.edgeFinset,pstar≤ρ e) →
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ v : V,∀ u u' : U,u≠u' →
          b≤transferSurvivalSum r hr P F
            (transferRootCompletedSpokes (rawWheelSpokes π d σ j) v) v u u' (fun e=>σ (Sum.inl e))) := by
  obtain ⟨c,hc,hcN⟩ := raw_ordinary_transfer_uniform_potential_event r hr α pstar hα hpstar hδ
  let b : ℝ := pstar^((1+2*r)*r)*c/2
  have hb : 0<b := by dsimp [b];positivity
  let ε : ℝ := min (pstar^2/4) (α*pstar^2/8)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  refine ⟨b,hb,?_⟩
  intro L hL d q₀ hd
  obtain ⟨N₀,hN₀⟩ := hcN L hL
  obtain ⟨N₁,hN₁⟩ := linear_deviation_failure_eventually_small 2 ((4*(d:ℝ)+3)^2*2) ε
    (by positivity) hε 3 (q₀+1)
  obtain ⟨N₂,hN₂⟩ := constant_deviation_failure_eventually_small 1
    ((r:ℝ)^2*((1+2*r)*r)) b (by
      have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
      positivity)
    hb 3 (q₀+1)
  refine ⟨max 2 (max N₀ (max N₁ N₂)),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hu P F π hP hF ρ hρ hρ1 hprob q hq hQ s hs hS j hnoshort pH hpHlo hj
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hsq : pstar^2≤pH^2 := by nlinarith only [hpstar,hpHlo]
  have hε₁ : ε≤pH^2/2 := by have hh := min_le_left (pstar^2/4) (α*pstar^2/8); dsimp [ε]; nlinarith only [hh,hsq,sq_nonneg pstar]
  have hε₂ : ε≤α*pH^2/4 := by
    have hh := min_le_right (pstar^2/4) (α*pstar^2/8)
    have hm := mul_le_mul_of_nonneg_left hsq hα.le
    dsimp [ε];nlinarith only [hh,hm,mul_pos hα (sq_pos_of_pos hpstar)]
  have hh := hN₀ V U Γ Color (by dsimp [n] at *;omega) hn P F π hP hF
    ρ hρ hρ1 d hd q hq hQ s hs hS j hnoshort pH hpHlo hj pstar (ε*n) b hpstar.le hpstar1
    (by positivity) hb
    (by nlinarith only [mul_le_mul_of_nonneg_right hε₁ hn0.le])
    (by nlinarith only [mul_le_mul_of_nonneg_right hε₂ hn0.le]) hprob
  have hM₁ := pair_neighbour_test_card (V:=V) (U:=U) hu hn (fun a : U×U=>a.1≠a.2)
  have hD₁ : (4*(d:ℝ)+3)^2*(2*(n:ℝ))≤(4*(d:ℝ)+3)^2*2*n := le_of_eq (by ring)
  have hf₁ := hN₁ n (by dsimp [n] at *;omega)
    ((Fintype.card {a : U×U // a.1≠a.2}:ℝ)*(n+1))
    ((4*(d:ℝ)+3)^2*(2*n)) (by positivity) (by simpa only [n,← Nat.card_eq_fintype_card] using hM₁) (by positivity) hD₁
  have hdom := paired_root_domain_card (V:=V) (U:=U) hu (fun a : U×U=>a.1≠a.2)
  have hf₂ := hN₂ n (by dsimp [n] at *;omega)
    (Fintype.card (V×{a : U×U // a.1≠a.2}):ℝ) (by positivity)
    (by simpa only [one_mul] using (show (Fintype.card (V×{a : U×U // a.1≠a.2}):ℝ)≤(n:ℝ)^3 by
      simp only [n,← Nat.card_eq_fintype_card] at hdom ⊢
      exact_mod_cast hdom))
  have hsum := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤
      1-((Fintype.card {a : U×U // a.1≠a.2}:ℝ)*(n+1))*
        (2*Real.exp (-2*(ε*n)^2/((4*(d:ℝ)+3)^2*(2*n))))-
      (Fintype.card (V×{a : U×U // a.1≠a.2}):ℝ)*
        (2*Real.exp (-2*b^2/((r:ℝ)^2*((1+2*r)*r)/n))) := by
    have htotal := add_le_add hf₁ hf₂
    have htotal' : _≤1/(n:ℝ)^q₀ := htotal.trans (by convert hsum using 1 <;> ring)
    linarith only [htotal']
  apply (hbound.trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ v u u' huu
  have hh := hσ v u u' huu
  dsimp only [b] at hh ⊢
  linarith only [hh]

end Oberwolfach
