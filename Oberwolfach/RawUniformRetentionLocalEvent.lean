module

public import Oberwolfach.UniformRetentionLocalConditionalEvent
public import Oberwolfach.RawUniformRetention

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_uniform_retention_local_event
    (d:ℕ) (hd:2≤d) (p ζ c δ:ℝ) (hp:0<p) (hζ:0<ζ) (hc:0<c) (hδ:0<δ):
    ∃m N:ℕ,1≤m ∧ 1≤N ∧ ∀(V U Γ Color:Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Nonempty V]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (H:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,(H i).card≤(A i).card) → (∀i∈T,c*((A i).card:ℝ)≤(H i).card) →
    ∀(π:Equiv.Perm V) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (g:Γ) (t₀:ℝ), (∀u,q u g=t₀) → p*Fintype.card V≤t₀*Fintype.card U →
    (∀i∈T,∀x,π x∈A i↔x∈A i) →
    1-δ≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>∀i∈T,RetainedRestrictionLocalGood π d z.1 g
        (startRetentionMinimum (rawStartHubSet π d z.1 g)) (A i) (H i) ζ z.2):=by
  obtain ⟨m,N₁,hm,hN₁,hCond⟩:=uniform_retention_local_conditional_event d (by omega) p ζ c (δ/2) hp hζ hc (by linarith)
  obtain ⟨N₂,hN₂⟩:=eventually_stretchedExp_le_inv_pow 4 1 (c:=2) (p:=1/5) (by norm_num) (by norm_num) 1
  obtain ⟨N₃,hN₃⟩:=exists_nat_gt (1/δ)
  let N:=max (max N₁ N₂) N₃
  have hN1:N₁≤N:=le_trans (le_max_left N₁ N₂) (le_max_left _ _)
  have hN2:N₂≤N:=le_trans (le_max_right N₁ N₂) (le_max_left _ _)
  have hN3:N₃≤N:=le_max_right _ _
  refine ⟨m,N,hm,le_trans hN₁ hN1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hu I T A H hmin hinj hHup hHlo π hnoshort q hq hQ s hs hS g t₀ hg hmass hInv
  let n:=Fintype.card V
  have hnpos:0<n:=by dsimp [n];omega
  have hnR:(0:ℝ)<n:=by exact_mod_cast hnpos
  have hmpos:0<Fintype.card U:=by
    by_contra hh
    have hz:Fintype.card U=0:=by omega
    rw [hz,Nat.cast_zero,mul_zero] at hmass
    have hpn:0<p*Fintype.card V:=by dsimp [n] at hnR;positivity
    linarith
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let E:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>∀x,
    |((rawStartHubSet π d σ g x).card:ℝ)-t₀*Fintype.card U/d|≤(n:ℝ)^(3/5:ℝ)
  let ν:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>
    startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g)) (startRetentionMinimum_le _)
  let Good:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>fun J=>
    ∀i∈T,RetainedRestrictionLocalGood π d σ g (startRetentionMinimum (rawStartHubSet π d σ g)) (A i) (H i) ζ J
  have he:0≤δ/2:=by linarith
  have hn3:(1/δ:ℝ)<n:=lt_of_lt_of_le hN₃ (by exact_mod_cast (le_trans hN3 hn))
  have hnδ:(1:ℝ)≤n*δ:=le_of_lt ((div_lt_iff₀ hδ).1 hn3)
  have hinv:(1:ℝ)/(2*n)≤δ/2:=by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*n)).2
    linarith only [hnδ]
  have hfirst:1-δ/2≤μ.probability E:=by
    have hh:=rawStartHubSet_common_event π d hd q hq hQ s hs hS hnoshort g t₀ hg ((n:ℝ)^(3/5:ℝ)) (by positivity)
    have hord:=retention_raw_failure_order n (Fintype.card U) hnpos hmpos hu
    have hf:=hN₂ n (by dsimp [n];omega)
    simp only [Real.rpow_one,pow_one] at hf
    have hb:2*n*Real.exp (-2*(n:ℝ)^(1/5:ℝ))≤δ/2:=by
      have heq:(1:ℝ)/(2*n)=((1:ℝ)/n)/2:=by ring
      rw [heq] at hinv
      have hinv':(1:ℝ)/n≤δ:=by linarith only [hinv]
      nlinarith only [hf,hinv']
    apply ((sub_le_sub_left (hord.trans hb) 1).trans hh).trans
    apply finiteLaw_probability_mono
    intro σ hσ x
    exact (hσ x).le
  have hsecond:∀σ,E σ→1-δ/2≤(ν σ).probability (Good σ):=by
    intro σ hσ
    exact hCond V U Γ Color (by omega) hu I T A H hmin hinj hHup hHlo π σ g (t₀*Fintype.card U/d)
      (div_le_div_of_nonneg_right hmass (by positivity)) hσ hInv
  have hh:=finiteLaw_twoStage_good μ ν E Good (δ/2) (δ/2) he he hfirst hsecond
  have hmon:(μ.sigma ν).probability (fun z=>E z.1 ∧ Good z.1 z.2)≤(μ.sigma ν).probability (fun z=>Good z.1 z.2):=
    by
      apply finiteLaw_probability_mono
      intro z hz
      exact hz.2
  change 1-δ≤(μ.sigma ν).probability (fun z=>Good z.1 z.2)
  linarith only [hh,hmon]
end Oberwolfach
