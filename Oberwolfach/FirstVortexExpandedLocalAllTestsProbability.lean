module

public import Oberwolfach.FirstVortexExpandedSixLocalTestsProbability
public import Oberwolfach.FirstVortexExpandedAllHubTestsProbability

@[expose] public section
/-! Both named local and all-hub tests hold together for one expanded sample
and its retained outcome, with an arbitrarily small prescribed failure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_expanded_local_all_tests_high_probability
    (d:ℕ) (hd:2≤d) (ε ρ₀ pRet ζ failure:ℝ)
    (hε:0<ε) (hεq:ε≤1/4) (hρ₀:0<ρ₀) (hpRet:0<pRet) (hζ:0<ζ) (hfailure:0<failure):
    ∃m₀ N:ℕ,1≤m₀ ∧ 1≤N ∧ ∀(V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0<Fintype.card V → (Fintype.card V:ℝ)/2≤D → 0<D →
    ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
    0≤β → β≤1/4 → 0<m → m₀≤m →
    ∀(π:Equiv.Perm V), (∀x,π x∈Q.extendedVertices 1↔x∈Q.extendedVertices 1) →
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t₀:ℝ) (hq0:∀u,q u false=t₀) (hmass:pRet*Fintype.card V≤t₀*Fintype.card U)
    (hspoke:∀u,(1/100:ℝ)≤s u false),
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z:Σω,Ret (f ω)=>FirstVortexExpandedSixLocalTests G π d D m β ε Q q s u ζ z ∧
        FirstVortexExpandedAllHubTests G π d D m β ε Q q s z) :=by
  obtain ⟨m₀,N₁,hm,hN₁,hSix⟩:=first_vortex_expanded_six_local_tests_high_probability d hd ε ρ₀ pRet ζ (failure/2)
    hε hεq hρ₀ hpRet hζ (by positivity)
  obtain ⟨N₂,hAll⟩:=first_vortex_expanded_all_hub_tests_high_probability d hd ε ρ₀ (failure/2) hε hρ₀ (by positivity)
  refine ⟨m₀,max N₁ N₂,hm,by omega,?_⟩
  intro V U _ _ _ _ _ hn hu G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π hpres p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass hspoke Ret ν μ f
  have ha:=hSix V U (by omega) hu G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π hpres
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass hspoke
  have hb:=hAll V U (by omega) hu G D m β Q hreg hV hD hρ hβ hβ1 hm π
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω)))
    (fun z=>FirstVortexExpandedSixLocalTests G π d D m β ε Q q s u ζ z)
    (fun z=>FirstVortexExpandedAllHubTests G π d D m β ε Q q s z) (failure/2) (failure/2) ha hb
  linarith only [hh]
end Oberwolfach
