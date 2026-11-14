module

public import Oberwolfach.RawIntervalUnassignedScaledHighProbability
public import Oberwolfach.RawIntervalUnassignedHighProbability
public import Oberwolfach.RawIntervalUnassignedCountsEvent
public import Oberwolfach.OrientationMargins

@[expose] public section
/-! High probability for fixed domains, at the n^(3/4) scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_unassigned_large_domain_high_probability (d:ℕ) (hd:2≤d) (fraction failure:ℝ) (hfraction:0<fraction) (hfailure:0<failure):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    Fintype.card U≤Fintype.card V→
    ∀ (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (A:Finset V) (J:Finset U),J.Nonempty→ fraction*(Fintype.card V:ℝ)≤A.card →
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<(A.card:ℝ)^(3/4:ℝ)) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<(A.card:ℝ)^(3/4:ℝ))) := by
  let a:ℝ:=fraction^(3/4:ℝ)
  have ha:0<a:=by dsimp [a];positivity
  obtain ⟨N,hN⟩:=raw_expanded_unassigned_fixed_domains_scaled_high_probability d hd a failure ha hfailure
  refine ⟨N,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν A J hJ hA μ f
  have hh:=hN V hn U Γ Color hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν A J hJ
  have hfrac:0≤fraction*(Fintype.card V:ℝ):=by positivity
  have hpow:=Real.rpow_le_rpow hfrac hA (by norm_num : (0:ℝ)≤3/4)
  have hbound:a*(Fintype.card V:ℝ)^(3/4:ℝ)≤(A.card:ℝ)^(3/4:ℝ):=by
    dsimp [a]
    rw [←Real.mul_rpow hfraction.le (Nat.cast_nonneg _)]
    exact hpow
  apply le_trans hh
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨fun u=>lt_of_lt_of_le (hz.1 u) hbound,fun v=>lt_of_lt_of_le (hz.2 v) hbound⟩
end Oberwolfach
