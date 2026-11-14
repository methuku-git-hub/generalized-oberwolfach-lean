module

public import Oberwolfach.MarkedReferenceEvent
public import Oberwolfach.MarkedReferenceConfigurations

@[expose] public section

/-! All reference degree, intersection, cut and configuration estimates
hold on one original marked sample. The configuration coefficient is chosen
before the errors and interval length. No test events are assumed independent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedReferenceCommonExponent (r : ℕ) (ε δ γ sstar tstar kstar κ : ℝ) (d : ℕ) : ℝ :=
  min (min (markedReferenceExponent ε δ γ kstar tstar κ d) (markedCutExponent γ kstar tstar κ d))
    (markedConfigurationExponent r γ sstar tstar kstar κ d)

theorem markedReferenceCommonExponent_pos (r : ℕ) (ε δ γ sstar tstar kstar κ : ℝ) (d : ℕ)
    (hε : 0<ε) (hδ : 0<δ) (hγ : 0<γ) (hsstar : 0<sstar) (htstar : 0<tstar)
    (hkstar : 0<kstar) (hκ : 0<κ) :
    0<markedReferenceCommonExponent r ε δ γ sstar tstar kstar κ d :=
  lt_min (lt_min (markedReferenceExponent_pos ε δ γ kstar tstar κ d hε hδ hγ hkstar htstar hκ)
    (markedCutExponent_pos γ kstar tstar κ d hγ hkstar htstar hκ))
    (markedConfigurationExponent_pos r γ sstar tstar kstar κ d hγ hsstar htstar hkstar hκ)

theorem marked_reference_common_event
    (r : ℕ) (hr : 1≤r) (γ sstar tstar kstar κ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (htstar1 : tstar≤1) (horder : tstar≤sstar)
    (hkstar : 0<kstar) (hκ : 0<κ) :
    ∃ β : ℝ,0<β ∧ ∀ ε δ : ℝ,0<ε → 0<δ → ∀ d : ℕ,∀ hd : 2≤d,
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
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
    1-106*(Fintype.card V:ℝ)^(r+8)*Real.exp
      (-markedReferenceCommonExponent r ε δ γ sstar tstar kstar κ d*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>(MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀ σ ∧
        MarkedReferenceCutFamilies P π d g j γ p k tstar σ) ∧
        MarkedReferenceConfigurations r P π d g j β σ) := by
  obtain ⟨β,hβ,hConfig⟩ := marked_configurations_raw_event r hr γ sstar tstar kstar κ
    hγ hγ1 hsstar htstar hkstar hκ
  refine ⟨β,hβ,?_⟩
  intro ε δ hε hδ d hd
  obtain ⟨NC,hNC⟩ := hConfig d hd
  obtain ⟨NR,hNR1,hNR⟩ := marked_reference_event ε δ γ kstar tstar κ hε hδ hγ hγ1 hkstar htstar htstar1 hκ d hd
  refine ⟨max NR NC,hNR1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P π hnoshort p k hp hk hsum hpmin hkmin D δP hδP hδε hPreg hP q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let cR := min (markedReferenceExponent ε δ γ kstar tstar κ d) (markedCutExponent γ kstar tstar κ d)
  let cC := markedConfigurationExponent r γ sstar tstar kstar κ d
  let errR := 72*(n:ℝ)^3*Real.exp (-cR*n)
  let errC := 34*(n:ℝ)^(r+8)*Real.exp (-cC*n)
  let μ : FiniteLaw (RawMarkedOutcome V U Γ Color) :=
    FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
  let Ref := fun σ : RawMarkedOutcome V U Γ Color=>MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀ σ ∧
    MarkedReferenceCutFamilies P π d g j γ p k tstar σ
  have hreference : 1-errR≤μ.probability Ref :=
    hNR V U Γ Color (by omega) hmlo hmhi P π hnoshort p k hp hk hsum hpmin hkmin D δP hδP hδε hPreg hP
      q hq hQ s hs hS g j s₀ t₀ hg hj (horder.trans hslo) htlo
  have hconfigs : 1-errC≤μ.probability (MarkedReferenceConfigurations r P π d g j β) :=
    hNC V U Γ Color (by omega) hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin
      q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  have hjoint := finiteLaw_good_intersection μ Ref (MarkedReferenceConfigurations r P π d g j β) errC hconfigs
  have hbase := (sub_le_sub_right hreference errC).trans hjoint
  have hsum := two_polynomial_exponential_errors_le (n:ℝ) 72 34 cR cC 3 (r+8) (r+8)
    (by exact_mod_cast hn) (by norm_num) (by norm_num) (by omega) (le_refl _)
  apply le_trans _ hbase
  change 1-106*(n:ℝ)^(r+8)*Real.exp (-min cR cC*n)≤1-errR-errC
  change errR+errC≤(72+34)*(n:ℝ)^(r+8)*Real.exp (-min cR cC*n) at hsum
  linarith only [hsum]

end Oberwolfach
