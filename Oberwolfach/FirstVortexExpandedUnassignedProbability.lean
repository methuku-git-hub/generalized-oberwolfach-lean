module

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

theorem raw_expanded_first_vortex_unassigned_high_probability (d:ℕ) (hd:2≤d) (ε ρ₀ failure:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hfailure:0<failure):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    Fintype.card U≤Fintype.card V→
    ∀ (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0<Fintype.card V → (Fintype.card V:ℝ)/2≤D →
    ρ₀ ≤ initialIndexDensity U D → 0≤β → β≤1/4 → 0<m →
    ∀ (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let A:=Q.extendedVertices 1
    let J:=Q.extendedIndices 1;
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<(A.card:ℝ)^(3/4:ℝ)) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<(A.card:ℝ)^(3/4:ℝ))) := by
  obtain ⟨N,hN⟩:=raw_expanded_unassigned_large_domain_high_probability d hd (ε/2) failure (by positivity) hfailure
  refine ⟨N,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hmn G D m β Q hreg hV hD hρ hβ hβ1 hm π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν A J μ f
  have hA:(ε/2)*(Fintype.card V:ℝ)≤(A.card:ℝ):=by
    have hh:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
    dsimp only [A]
    linarith
  have hJ:J.Nonempty:=Q.first_inner_indices_nonempty hreg hV hD hρ₀ hρ hβ hβ1 hε hm
  exact hN V hn U Γ Color hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν A J hJ hA
end Oberwolfach
