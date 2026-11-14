module

public import Oberwolfach.RetentionRestrictionCommonEvent
public import Oberwolfach.RetentionRateMargins
public import Oberwolfach.BinomialRestrictionMargins

@[expose] public section

/-! Uniform retention on all fixed restrictions, conditional on the raw
start-count event. The size thresholds precede graphs, domains and outcomes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_retention_conditional_event
    (d C Q : ℕ) (hd : 0<d) (p ζ : ℝ) (hp : 0<p) (hζ : 0<ζ) :
    ∃ m N : ℕ,1≤m ∧ 1≤N ∧ ∀ (V U Γ Color I : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I] [Nonempty V]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → Fintype.card I≤(Fintype.card V)^C →
    ∀ (π : Equiv.Perm V) (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (μ : ℝ),
      p*Fintype.card V/d≤μ →
      (∀ a,|((rawStartHubSet π d σ g a).card:ℝ)-μ|≤(Fintype.card V:ℝ)^(3/5:ℝ)) →
    ∀ (S : I→Finset V) (T : I→Finset U),
      (∀ i x,π x∈S i ↔ x∈S i) → (∀ i,m≤(S i).card) → (∀ i,m≤(T i).card) →
    1-1/(2*(Fintype.card V:ℝ)^Q)≤
      (startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g))
        (startRetentionMinimum_le _)).probability
        (RetainedRestrictionGood π d σ g (startRetentionMinimum (rawStartHubSet π d σ g)) S T ζ) := by
  let K : ℝ := 4*d/p
  let a : ℝ := ζ/(d+1:ℕ)
  have hK : 0≤K := by dsimp [K];positivity
  have ha : 0<a := by dsimp [a];positivity
  obtain ⟨m,N₁,hm,hN₁1,hN₁⟩ := uniform_binomial_restriction_tail K a (2/5) hK ha (by norm_num) (C+Q+3)
  obtain ⟨N₂,hN₂1,hN₂⟩ := eventually_retention_error_small p hp d hd
  refine ⟨m,max N₁ (max N₂ (2*(d+2))),hm,hN₁1.trans (le_max_left _ _),?_⟩
  intro V U Γ Color I _ _ _ _ _ _ _ _ hn hu hI π σ g μ hμ hcounts S T hS hSc hTc
  let n := Fintype.card V
  have hnpos : 0<n := by dsimp [n];omega
  let A := rawStartHubSet π d σ g
  let p' := K*(n:ℝ)^(-2/5:ℝ)
  have hp' : 0≤p' := by dsimp [p'];positivity
  have hrate (v : V) : (((A v).card-startRetentionMinimum A:ℕ):ℝ)/(A v).card≤p' :=
    startRetentionMinimum_polynomial_rate A n d hnpos hd p μ hp hμ (hN₂ n (by dsimp [n];omega)) hcounts v
  have htail (M : ℕ) (hM : m≤M) :
      (M.choose (Nat.ceil (ζ*M/(d+1:ℕ))):ℝ)*p'^(Nat.ceil (ζ*M/(d+1:ℕ)))≤1/(n:ℝ)^(C+Q+3) := by
    have hh := hN₁ n (by dsimp [n];omega) M hM p' hp' (by dsimp [p'];simp only [neg_div];exact le_refl _)
    have he : a*M=ζ*M/(d+1:ℕ) := by dsimp [a];ring
    simpa only [he] using hh
  have hh := retainedRestriction_common_event π d σ g (startRetentionMinimum A) (startRetentionMinimum_le A)
    S T hS ζ p' (1/(n:ℝ)^(C+Q+3)) hζ.le hp' hrate (fun i=>htail _ (hSc i)) (fun i=>htail _ (hTc i))
  have herror := retention_restriction_union_margin d C Q n (by dsimp [n];omega) (Fintype.card I) (Fintype.card U) hI hu
  exact (sub_le_sub_left herror 1).trans hh

end Oberwolfach
