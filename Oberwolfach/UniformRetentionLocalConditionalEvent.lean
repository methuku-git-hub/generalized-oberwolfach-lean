module

public import Oberwolfach.RetentionRestrictionLocalSmallFailure
public import Oberwolfach.UniformRetentionConditionalEvent

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_retention_local_conditional_event
    (d:ℕ) (hd:0<d) (p ζ c δ:ℝ) (hp:0<p) (hζ:0<ζ) (hc:0<c) (hδ:0<δ):
    ∃m N:ℕ,1≤m ∧ 1≤N ∧ ∀(V U Γ Color:Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Nonempty V]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (H:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,(H i).card≤(A i).card) → (∀i∈T,c*((A i).card:ℝ)≤(H i).card) →
    ∀(π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (μ:ℝ),
    p*Fintype.card V/d≤μ →
    (∀x,|((rawStartHubSet π d σ g x).card:ℝ)-μ|≤(Fintype.card V:ℝ)^(3/5:ℝ)) →
    (∀i∈T,∀x,π x∈A i↔x∈A i) →
    1-δ≤(startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g))
      (startRetentionMinimum_le (rawStartHubSet π d σ g))).probability
      (fun J=>∀i∈T,RetainedRestrictionLocalGood π d σ g (startRetentionMinimum (rawStartHubSet π d σ g)) (A i) (H i) ζ J):=by
  let K:ℝ:=4*d/p
  have hK:0≤K:=by dsimp [K];positivity
  obtain ⟨m,hm,hLocal⟩:=retained_restriction_local_family_small_failure d ζ K (2/5) c δ hζ hK (by norm_num) hc hδ
  obtain ⟨N,hN,hN₂⟩:=eventually_retention_error_small p hp d hd
  refine ⟨m,N,hm,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hu I T A H hmin hinj hHup hHlo π σ g μ hμ hcounts hInv
  let n:=Fintype.card V
  have hnpos:0<n:=by dsimp [n];omega
  let Astart:=rawStartHubSet π d σ g
  let p':=K*(n:ℝ)^(-2/5:ℝ)
  have hp':0≤p':=by dsimp [p'];positivity
  have hrate (v:V):(((Astart v).card-startRetentionMinimum Astart:ℕ):ℝ)/(Astart v).card≤p':=
    startRetentionMinimum_polynomial_rate Astart n d hnpos hd p μ hp hμ (hN₂ n (by dsimp [n];omega)) hcounts v
  apply hLocal V U Γ Color I T A H n hmin hinj hHup hHlo (by intro i hi;exact Finset.card_le_univ (A i)) π hInv σ g
    (startRetentionMinimum Astart) (startRetentionMinimum_le Astart) p' hp' (by dsimp [p']; simp only [neg_div]; exact le_rfl) hrate
end Oberwolfach
