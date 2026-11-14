module

public import Oberwolfach.UniformRetentionConditionalEvent
public import Oberwolfach.RawStartCounts
public import Oberwolfach.DependentGoodEvents

@[expose] public section

/-! The actual two-stage raw interval law followed by uniform retention.
Only one interval colour is trimmed, with its retained size chosen from
that raw outcome. The entire fixed restriction family shares this sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev RawRetainedIntervalOutcome {V U Γ Color : Type} [Fintype V] [Fintype U]
    [Fintype Γ] [Fintype Color] [Nonempty V] [DecidableEq V] [DecidableEq U]
    (π : Equiv.Perm V) (d : ℕ) (g : Γ) :=
  Σ σ : RawIntervalFamilyOutcome V U Γ Color,
    StartRetentionOutcome (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g))

def rawUniformRetentionLaw {V U Γ Color : Type} [Fintype V] [Fintype U]
    [Fintype Γ] [Fintype Color] [Nonempty V] [DecidableEq V] [DecidableEq U]
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (g : Γ)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) :
    FiniteLaw (RawRetainedIntervalOutcome (U:=U) (Color:=Color) π d g) :=
  (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).sigma
    (fun σ=>startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g))
      (startRetentionMinimum_le _))

theorem raw_uniform_retention_restrictions (d C Q : ℕ) (hd : 2≤d)
    (p ζ : ℝ) (hp : 0<p) (hζ : 0<ζ) :
    ∃ m N : ℕ,1≤m ∧ 1≤N ∧ ∀ (V U Γ Color I : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I] [Nonempty V]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → Fintype.card I≤(Fintype.card V)^C →
    ∀ (π : Equiv.Perm V), (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (t₀ : ℝ),(∀ u,q u g=t₀) → p*Fintype.card V≤t₀*Fintype.card U →
    ∀ (S : I→Finset V) (T : I→Finset U),
      (∀ i x,π x∈S i ↔ x∈S i) → (∀ i,m≤(S i).card) → (∀ i,m≤(T i).card) →
    1-1/(Fintype.card V:ℝ)^Q≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>(∀ a,|((rawStartHubSet π d z.1 g a).card:ℝ)-t₀*Fintype.card U/d|≤(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
        RetainedRestrictionGood π d z.1 g (startRetentionMinimum (rawStartHubSet π d z.1 g)) S T ζ z.2) := by
  obtain ⟨m,N₁,hm,hN₁1,hN₁⟩ := uniform_retention_conditional_event d C Q (by omega) p ζ hp hζ
  obtain ⟨N₂,hN₂⟩ := eventually_stretchedExp_le_inv_pow 4 1 (c:=2) (p:=1/5) (by norm_num) (by norm_num) Q
  refine ⟨m,max N₁ N₂,hm,hN₁1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color I _ _ _ _ _ _ _ _ hn hu hI π hnoshort q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc
  let n := Fintype.card V
  have hnpos : 0<n := by dsimp [n];omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hnpos
  have hmpos : 0<Fintype.card U := by
    by_contra hh
    have hz : Fintype.card U=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hmass
    have hpn : 0<p*Fintype.card V := by dsimp [n] at hnR;positivity
    linarith
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let E := fun σ : RawIntervalFamilyOutcome V U Γ Color=>
    ∀ a,|((rawStartHubSet π d σ g a).card:ℝ)-t₀*Fintype.card U/d|≤(n:ℝ)^(3/5:ℝ)
  let ν := fun σ : RawIntervalFamilyOutcome V U Γ Color=>
    startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g))
      (startRetentionMinimum_le _)
  let Good := fun σ : RawIntervalFamilyOutcome V U Γ Color=>
    RetainedRestrictionGood π d σ g (startRetentionMinimum (rawStartHubSet π d σ g)) S T ζ
  let e := 1/(2*(n:ℝ)^Q)
  have he : 0≤e := by dsimp [e];positivity
  have hfirst : 1-e≤μ.probability E := by
    have hh := rawStartHubSet_common_event π d hd q hq hQ s hs hS hnoshort g t₀ hg
      ((n:ℝ)^(3/5:ℝ)) (by positivity)
    have hord := retention_raw_failure_order n (Fintype.card U) hnpos hmpos hu
    have hf := hN₂ n (by dsimp [n];omega)
    simp only [Real.rpow_one] at hf
    have hb : 2*n*Real.exp (-2*(n:ℝ)^(1/5:ℝ))≤e := by
      have heq : 1/(n:ℝ)^Q=2*e := by dsimp [e];ring
      rw [heq] at hf
      linarith only [hf]
    apply ((sub_le_sub_left (hord.trans hb) 1).trans hh).trans
    apply finiteLaw_probability_mono
    intro σ hσ a
    exact (hσ a).le
  have hsecond : ∀ σ,E σ → 1-e≤(ν σ).probability (Good σ) := by
    intro σ hσ
    exact hN₁ V U Γ Color I (by omega) hu hI π σ g (t₀*Fintype.card U/d)
      (div_le_div_of_nonneg_right hmass (by positivity)) hσ S T hInv hSc hTc
  have hh := finiteLaw_twoStage_good μ ν E Good e e he he hfirst hsecond
  have heq : 1-e-e=1-1/(n:ℝ)^Q := by dsimp [e];ring
  rw [heq] at hh
  exact hh

end Oberwolfach
