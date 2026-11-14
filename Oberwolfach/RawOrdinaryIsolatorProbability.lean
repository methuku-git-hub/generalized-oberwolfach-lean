module

public import Oberwolfach.RawOrdinaryIsolatorUniformEvent
public import Oberwolfach.RawOrdinaryIsolatorCounts
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! Uniform potential isolator bounds, including both root spokes but omitting
its physical root edge. Constants precede the interval length and the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_ordinary_isolator_uniform_probability
    (α pstar ω : ℝ) (hα : 0<α) (hα1 : α≤1) (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) :
    ∃ K : ℕ,2≤K ∧ ∀ k : ℕ,K≤k → ∃ b : ℝ,0<b ∧
    ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d, ∃ N : ℕ,
    ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V →
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (π : Equiv.Perm V) (θ : ℝ),0≤θ → θ+α/2≤1 →
    (∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
    ∀ (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1),
      (∀ e∈P.edgeFinset,pstar≤ρ e) →
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x y : V,x≠y → ¬F.Adj x y →
          b≤ordinaryIsolatorPotential P F (rawWheelSpokes π d σ j)
            (2+k) θ (α/4) x y (fun e=>σ (Sum.inl e))) := by
  obtain ⟨K,hK,hKc⟩ := raw_ordinary_isolator_uniform_potential_event α pstar hα hα1 hpstar
  refine ⟨K,hK,?_⟩
  intro k hk
  obtain ⟨c,hc,hcN⟩ := hKc k hk
  let a : ℝ := pstar^((2+k)^2)*c/2
  have ha : 0<a := by dsimp [a];positivity
  let b : ℝ := a*(pstar^2*ω/2)
  have hb : 0<b := by dsimp [b];positivity
  let ε : ℝ := min (pstar/4) (α*pstar/8)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  let εH : ℝ := pstar^2*ω/2
  have hεH : 0<εH := by dsimp [εH];positivity
  refine ⟨b,hb,?_⟩
  intro L hL d q₀ hd
  obtain ⟨N₀,hN₀⟩ := hcN L hL
  obtain ⟨N₁,hN₁⟩ := linear_deviation_failure_eventually_small 2 ((4*(d:ℝ)+3)^2) ε
    (by positivity) hε 2 (q₀+1)
  obtain ⟨N₂,hN₂⟩ := constant_deviation_failure_eventually_small 1 (((2+k:ℕ):ℝ)^2) a
    (by positivity) ha 3 (q₀+1)
  obtain ⟨N₃,hN₃⟩ := linear_deviation_failure_eventually_small 1 ((4*(d:ℝ)+3)^2*2) εH
    (by positivity) hεH 2 (q₀+1)
  refine ⟨max 3 (max N₀ (max N₁ (max N₂ N₃))),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P F π θ hθ hθ1 hP hF hclose
    ρ hρ hρ1 hprob q hq hQ s hs hS j hnoshort pH hpHlo hj
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<Fintype.card U := by exact_mod_cast hm0
  have hsq : pstar^2≤pH^2 := by nlinarith [hpstar,hpHlo]
  have hε₁ : ε≤pH/2 := by have hh := min_le_left (pstar/4) (α*pstar/8);dsimp [ε];linarith
  have hε₂ : ε≤α*pH/4 := by
    have hh := min_le_right (pstar/4) (α*pstar/8)
    have hm := mul_le_mul_of_nonneg_left hpHlo hα.le
    dsimp [ε];nlinarith only [hh,hm,mul_pos hα hpstar]
  have hh := hN₀ V U Γ Color (by dsimp [n] at *;omega) hn P F π θ hθ hθ1 hP hF
    ρ hρ hρ1 d hd q hq hQ s hs hS j hnoshort pH hpHlo hj pstar (ε*n) a hpstar.le hpstar1
    (by positivity) ha
    (by nlinarith only [mul_le_mul_of_nonneg_right hε₁ hn0.le])
    (by nlinarith only [mul_le_mul_of_nonneg_right hε₂ hn0.le]) hprob
  let b₁ := ((Fintype.card U:ℝ)*(n+1))*(2*Real.exp (-2*(ε*n)^2/((4*(d:ℝ)+3)^2*n)))
  let b₂ := (Fintype.card ({a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}×U):ℝ)*
    (2*Real.exp (-2*a^2/(((2+k:ℕ):ℝ)^2/n)))
  have hperhub : 1-(b₁+b₂)≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x y : V,x≠y → ¬F.Adj x y → ∀ u : U,
          a≤rootedInducedSurvivalSum P
            (fun S : OrdinaryIsolatorCandidate P F (rawWheelSpokes π d σ j) (2+k) θ (α/4) x y u=>S.val)
            s(x,y) (fun e=>σ (Sum.inl e))) := by
    apply ((le_of_eq (sub_add_eq_sub_sub 1 b₁ b₂)).trans hh).trans
    apply finiteLaw_probability_mono
    intro σ hσ x y hxy hfxy u
    have hh := hσ x y hxy hfxy u
    dsimp only [a] at hh ⊢;linarith
  have hhubmargin : εH*n≤pH^2*ω*n/2 := by
    have hm := mul_le_mul_of_nonneg_right hsq (mul_nonneg hω.le hn0.le)
    dsimp [εH];nlinarith only [hm]
  have hcount := raw_ordinary_isolator_count_event P F π ρ hρ hρ1 d hd q hq hQ s hs hS
    hnoshort hclose hn hm j pH hj (2+k) (by omega) θ (α/4) a ω (b₁+b₂) (εH*n)
    ha.le (by positivity) hmlo hhubmargin hperhub
  have hdom : (Fintype.card {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}:ℝ)≤(n:ℝ)^2 := by
    have hh := Fintype.card_subtype_le (fun a : V×V=>a.1≠a.2 ∧ ¬F.Adj a.1 a.2)
    rw [Fintype.card_prod] at hh
    simpa only [pow_two] using (show (Fintype.card {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}:ℝ)≤(n:ℝ)*n by exact_mod_cast hh)
  have hmhiR : (Fintype.card U:ℝ)≤n := by exact_mod_cast hmhi
  have hf₁ := hN₁ n (by dsimp [n] at *;omega) ((Fintype.card U:ℝ)*(n+1))
    ((4*(d:ℝ)+3)^2*n) (by positivity)
    (by have hh := mul_le_mul_of_nonneg_right hmhiR (by positivity : (0:ℝ)≤n+1);nlinarith)
    (by positivity) le_rfl
  have hf₂ := hN₂ n (by dsimp [n] at *;omega)
    (Fintype.card ({a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}×U):ℝ) (by positivity)
    (by rw [Fintype.card_prod,Nat.cast_mul];have hh := mul_le_mul hdom hmhiR (by positivity) (by positivity);nlinarith only [hh])
  have hf₃ := hN₃ n (by dsimp [n] at *;omega)
    (Fintype.card {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}:ℝ)
    ((4*(d:ℝ)+3)^2*(2*Fintype.card U)) (by positivity) (by simpa only [one_mul] using hdom)
    (by positivity)
    (by have hh := mul_le_mul_of_nonneg_left hmhiR (by positivity : (0:ℝ)≤(4*(d:ℝ)+3)^2*2);nlinarith only [hh])
  have hsum := scaled_inverse_power_le n q₀ hn 3 (by exact_mod_cast (show 3≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤1-(b₁+b₂)-
      (Fintype.card {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}:ℝ)*
        (2*Real.exp (-2*(εH*n)^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U)))) := by
    dsimp only [b₁,b₂]
    simp only [← Nat.card_eq_fintype_card] at hf₁ hf₂ hf₃ hsum ⊢
    have htotal := add_le_add (add_le_add hf₁ hf₂) hf₃
    have htotal' : _≤1/(n:ℝ)^q₀ := htotal.trans (by convert hsum using 1 <;> ring)
    linarith only [htotal']
  apply (hbound.trans hcount).trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy hfxy
  have hh := (hσ x y hxy hfxy).1
  have hm := mul_le_mul_of_nonneg_left hsq (mul_nonneg ha.le hω.le)
  dsimp only [b]
  nlinarith only [hh,hm]

end Oberwolfach
