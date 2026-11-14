module

public import Oberwolfach.MarkedReferenceEvent
public import Oberwolfach.MarkedSeedDensities

@[expose] public section

/-! The marked reference event with the manuscript's fixed lower densities
and actual formulas p = rho*s/2, k = p/m, t = s/m. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_actual_densities
    (m : ℕ) (hm : 1≤m) (ε δ γ κ ρstar sstar : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hγ : 0<γ) (hγ1 : γ≤1/2)
    (hκ : 0<κ) (hρstar : 0<ρstar) (hsstar : 0<sstar) (hsstar1 : sstar≤1/100)
    (d : ℕ) (hd : 2≤d) :
    let kstar := ρstar*sstar/(2*m)
    let tstar := sstar/m
    let c := min (markedReferenceExponent ε δ γ kstar tstar κ d) (markedCutExponent γ kstar tstar κ d)
    0<c ∧ ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → κ*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ ρ s₀ : ℝ,ρstar≤ρ → ρ≤1 → sstar≤s₀ → s₀≤1/100 →
    ∀ δP : ℝ,0≤δP → δP≤ε/4 →
      (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/ρ|≤δP*Fintype.card V) →
      (∀ x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color),(∀ u,q u g=s₀/m) → (∀ u,s u j=s₀) →
    ∀ (hp : 0≤ρ*s₀/2) (hk : 0≤(ρ*s₀/2)/m) (hsum : 2*(ρ*s₀/2)+2*((ρ*s₀/2)/m)≤1),
    1-72*(Fintype.card V:ℝ)^3*Real.exp (-c*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw (ρ*s₀/2) ((ρ*s₀/2)/m) hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>MarkedReferenceStatistics P π d g j (2*Fintype.card U/ρ) ε δ γ (ρ*s₀/2) ((ρ*s₀/2)/m) s₀ (s₀/m) σ ∧
        MarkedReferenceCutFamilies P π d g j γ (ρ*s₀/2) ((ρ*s₀/2)/m) tstar σ) := by
  intro kstar tstar c
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hkstar : 0<kstar := by dsimp [kstar];positivity
  have htstar : 0<tstar := by dsimp [tstar];positivity
  have htstar1 : tstar≤1 := by
    dsimp [tstar]
    apply (div_le_iff₀ hm0).mpr
    linarith
  refine ⟨lt_min
    (markedReferenceExponent_pos ε δ γ kstar tstar κ d hε hδ hγ hkstar htstar hκ)
    (markedCutExponent_pos γ kstar tstar κ d hγ hkstar htstar hκ),?_⟩
  obtain ⟨N,hN1,hN⟩ := marked_reference_event ε δ γ kstar tstar κ hε hδ hγ hγ1 hkstar htstar htstar1 hκ d hd
  refine ⟨N,hN1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hmlo hmhi P π hnoshort ρ s₀ hρlo hρhi hslo hshi δP hδP hδε hPreg hP q hq hQ s hs hS g j hg hj hp hk hsum
  have hden := marked_seed_density_bounds m hm ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
  have htlo : tstar≤s₀/m := div_le_div_of_nonneg_right hslo hm0.le
  have htordinary : tstar≤s₀ := by
    have hss : sstar/m≤sstar := (div_le_iff₀ hm0).mpr (by nlinarith only [hm1,hsstar])
    exact hss.trans hslo
  exact hN V U Γ Color hn hmlo hmhi P π hnoshort (ρ*s₀/2) ((ρ*s₀/2)/m)
    hp hk hsum hden.2.1 hden.2.2.1 (2*Fintype.card U/ρ) δP hδP hδε hPreg hP
    q hq hQ s hs hS g j s₀ (s₀/m) hg hj htordinary htlo

end Oberwolfach
