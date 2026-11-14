module

public import Oberwolfach.OrdinaryFullHostLoadMargins
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section

/-! Uniform target-one error margins for the full-host load event. The degree
error is fixed before the interval length and the conflict-degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinaryFullHostSeed_uniform_probability
    (r : ℕ) (hr : 3≤r) (pstar ω c B η : ℝ)
    (hpstar : 0<pstar) (hω : 0<ω) (hc : 0≤c) (hB : 0<B) (hη : 0<η) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V →
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (π : Equiv.Perm V),
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pR pH D₀ ε : ℝ,∀ hRlo : pstar≤pR,∀ hRhi : pR≤1,pstar≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D₀ → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
    ∀ weight : OrdinaryCycle P r → ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2)) →
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
    let μ := rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi)
      d hd q hq hQ s hs hS
    let w := ordinaryFullHostSeed (U:=U) P F r weight pR pH
    1-1/(Fintype.card V:ℝ)^q₀≤(FiniteLaw.pi μ).probability (fun σ=>
      (∀ x y,P.Adj x y → ¬F.Adj x y →
        |ordinaryPotentialLoad w (Sum.inl s(x,y)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤η) ∧
      (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤η)) := by
  refine ⟨η/8,by positivity,?_⟩
  intro L hL d q₀ hd
  let Bplus := B/(ω*pstar^(2*r-1))
  have hBp : 0<Bplus := by dsimp [Bplus];positivity
  obtain ⟨N₁,hN₁⟩ := ordinary_load_failure_eventually_small r d q₀ (by omega) Bplus (η/4) hBp (by positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_constant_le_linear (48*(r:ℝ)^4*B*L) η hη
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P F π hF hclose hnoshort
    pR pH D₀ ε hRlo hRhi hHlo hHhi hD hε hε₀ hdeg hbalance q hq hQ s hs hS j hj weight hw he μ w
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<Fintype.card U := by exact_mod_cast hm0
  have hh := ordinaryFullHostSeed_common_event P F r (by omega) π d hd hclose hnoshort
    pR pH ω pstar c B L D₀ ε hn hm hω hpstar hmlo hmhi hRlo hRhi hHlo hHhi hc hB hL hF hD hε hdeg hbalance
    q hq hQ s hs hS j hj weight hw he (η/4) (by positivity)
  have htail := hN₁ n (by dsimp [n] at *;omega) (Fintype.card (Sym2 V⊕(V×U)):ℝ) (by positivity)
    (by exact_mod_cast ordinary_resource_domain_card hmhi)
  have hscale := hN₂ n (by dsimp [n] at *;omega)
  have herror : 12*(r:ℝ)^4*B*L/n≤η/4 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hscale]
  have herror₅ : 5*(r:ℝ)^4*B*L/n≤η/4 := by
    have hh : 5*(r:ℝ)^4*B*L/n≤12*(r:ℝ)^4*B*L/n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg r) 4) hB.le) hL]
    exact hh.trans herror
  have hbound : 1-1/(n:ℝ)^q₀≤1-(Fintype.card (Sym2 V⊕(V×U)):ℝ)*
    (2*Real.exp (-2*(η/4)^2/((4*(d:ℝ)+3)^2*((r:ℝ)^4*Bplus/n)*(2*r)*((r:ℝ)^2*Bplus)))) := by linarith only [htail]
  apply (hbound.trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  constructor
  · intro x y hxy hfxy
    have hh := hσ.1 x y hxy hfxy
    dsimp only [n] at herror₅
    linarith only [hh,herror₅,hη]
  · intro v u
    have hh := hσ.2 v u
    dsimp only [n] at herror
    linarith only [hh,herror,hε₀,hη]

end Oberwolfach
