module

public import Oberwolfach.MarkedReferenceStatistics
public import Oberwolfach.ExponentialMarkedReferenceCuts
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Complete reference degree, intersection and cut estimates on one raw
marked sample, with an exponential bound uniform over the host and arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_event
    (ε δ γ kstar tstar κ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hγ : 0<γ) (hγ1 : γ≤1/2)
    (hkstar : 0<kstar) (htstar : 0<tstar) (htstar1 : tstar≤1) (hκ : 0<κ) (d : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → κ*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ D δP : ℝ,0≤δP → δP≤ε/4 →
      (∀ x,|(P.degree x:ℝ)-D|≤δP*Fintype.card V) →
      (∀ x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → tstar≤s₀ → tstar≤t₀ →
    1-72*(Fintype.card V:ℝ)^3*Real.exp
      (-min (markedReferenceExponent ε δ γ kstar tstar κ d) (markedCutExponent γ kstar tstar κ d)*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀ σ ∧
        MarkedReferenceCutFamilies P π d g j γ p k tstar σ) := by
  obtain ⟨NS,hNS⟩ := marked_reference_statistics ε δ γ kstar tstar κ hε hδ hγ hkstar htstar hκ d hd
  obtain ⟨NC,hNC1,hNC⟩ := marked_reference_cut_event γ kstar tstar κ hγ hγ1 hkstar htstar htstar1 hκ d hd
  refine ⟨max NS NC,hNC1.trans (le_max_right _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P π hnoshort p k hp hk hsum hpmin hkmin D δP hδP hδε hPreg hP q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  let n : ℝ := Fintype.card V
  let cS := markedReferenceExponent ε δ γ kstar tstar κ d
  let cC := markedCutExponent γ kstar tstar κ d
  let c := min cS cC
  have hn1 : 1≤n := by dsimp [n];exact_mod_cast (show 1≤Fintype.card V by omega)
  have hn0 : 0≤n := Nat.cast_nonneg _
  let μ : FiniteLaw (RawMarkedOutcome V U Γ Color) := FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
  have hstats : 1-36*n^3*Real.exp (-cS*n)≤
      μ.probability (MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀) :=
    hNS V U Γ Color (by omega) hmlo hmhi P π hnoshort p k hp hk hsum hpmin D δP hδP hδε hPreg hP
      q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  have hcuts : 1-36*n*Real.exp (-cC*n)≤
      μ.probability (MarkedReferenceCutFamilies P π d g j γ p k tstar) :=
    hNC V U Γ Color (by omega) hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin
      q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  have hjoint := finiteLaw_good_intersection μ
    (MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀)
    (MarkedReferenceCutFamilies P π d g j γ p k tstar) (36*n*Real.exp (-cC*n)) hcuts
  have hbase := (sub_le_sub_right hstats (36*n*Real.exp (-cC*n))).trans hjoint
  have heS : Real.exp (-cS*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left cS cC) hn0
    change c*n≤cS*n at hh
    linarith only [hh]
  have heC : Real.exp (-cC*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right cS cC) hn0
    change c*n≤cC*n at hh
    linarith only [hh]
  have hpow : n≤n^3 := by
    have h12 : n≤n^2 := by nlinarith only [hn1]
    have h23 : n^2≤n^3 := by nlinarith only [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn1)]
    exact h12.trans h23
  have hbS := mul_le_mul_of_nonneg_left heS (show 0≤36*n^3 by positivity)
  have hbC : 36*n*Real.exp (-cC*n)≤36*n^3*Real.exp (-c*n) :=
    mul_le_mul (by linarith only [hpow]) heC (by positivity) (by positivity)
  apply le_trans _ hbase
  change 1-72*n^3*Real.exp (-c*n)≤_
  linarith only [hbS,hbC]

end Oberwolfach
