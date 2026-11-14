module

public import Oberwolfach.FirstVortexExpandedAllHubTests

@[expose] public section
/-! The named all-hub tests hold with high probability on the same expanded
sample and retention outcome used in the long construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_expanded_all_hub_tests_high_probability
    (d:ℕ) (hd:2≤d) (ε ρ₀ failure:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hfailure:0<failure):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
    ρ₀≤ initialIndexDensity U D→0≤β→β≤1/4→0<m→
    ∀(π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z:Σω,Ret (f ω)=>FirstVortexExpandedAllHubTests G π d D m β ε Q q s z):=by
  obtain ⟨N,hN⟩:=raw_expanded_first_vortex_unassigned_all_hubs_high_probability d hd ε ρ₀ failure hε hρ₀ hfailure
  refine ⟨N,?_⟩
  intro V U _ _ _ _ _ hn hu G D m β Q hreg hV hD hρ hβ hβ1 hm π p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort Ret ν μ f
  have h:=hN V hn U Bool Bool hu G D m β Q hreg hV hD hρ hβ hβ1 hm π
    p k p₂ k₂ u hp hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort Ret ν
  simpa only [FirstVortexExpandedAllHubTests] using h
end Oberwolfach
