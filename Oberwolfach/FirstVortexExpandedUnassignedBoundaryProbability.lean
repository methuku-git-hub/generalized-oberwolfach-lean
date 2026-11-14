module

public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.FirstVortexExpandedBoundaryProbability
public import Oberwolfach.FirstVortexExpandedUnassignedProbability
public import Oberwolfach.FirstVortexIndicesNonempty
public import Oberwolfach.RawIntervalUnassignedLargeDomainProbability
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

theorem raw_expanded_first_vortex_unassigned_boundary_high_probability (d:ℕ) (hd:2≤d) (ε ρ₀ failure:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hfailure:0<failure):
    ∃m₀:ℕ,1≤m₀ ∧ ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Color:Type) [Fintype U] [Fintype Color] [DecidableEq U],
    Fintype.card U≤Fintype.card V→
    ∀ (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0<Fintype.card V → (Fintype.card V:ℝ)/2≤D → 0<D →
    ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 → 0≤β → β≤1/4 → 0<m → m₀≤(Q.extendedVertices 1).card →
    ∀ (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Bool Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let A:=Q.extendedVertices 1
    let J:=Q.extendedIndices 1;
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<(A.card:ℝ)^(3/4:ℝ)) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<(A.card:ℝ)^(3/4:ℝ)) ∧
      (∀v∈A,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) J v).card:ℝ)≤
        4*((J.card):ℝ)/d+4*((A.card):ℝ)^(3/4:ℝ))) := by
  obtain ⟨N,hN⟩:=raw_expanded_first_vortex_unassigned_high_probability d hd ε ρ₀ (failure/2) hε hρ₀ (by positivity)
  obtain ⟨m₀,hm₀,hBound⟩:=raw_expanded_first_vortex_boundary_high_probability d hd ε ρ₀ (failure/2) hε hρ₀ (by positivity)
  refine ⟨m₀,hm₀,N,?_⟩
  intro V _ _ hn U Color _ _ _ hmn G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν A J μ f
  have hUnassign:=hN V hn U Bool Color hmn G D m β Q hreg hV hD hρ hβ hβ1 hm π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  have hb:=hBound V U Color G D m β Q hreg hV hD hDpos hρ hρhi hβ hβ1 hm hsize π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) _ _ (failure/2) (failure/2) hUnassign hb
  simp only [and_assoc] at hh
  linarith only [hh]
end Oberwolfach
