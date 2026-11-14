module

public import Oberwolfach.FirstVortexExpandedBoundaryAllRootsCommon
public import Oberwolfach.FirstVortexAllRootsBoundaryRelative
public import Oberwolfach.FiniteLawUniformEventReorder
public import Oberwolfach.FirstVortexIndicesNonempty
public import Oberwolfach.ExpandedBoundaryHubsLocalSmallFailure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_first_vortex_boundary_relative_with_event
    (d:ℕ) (hd:2≤d) (ε ρ₀ failure c:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hfailure:0<failure) (hc:0<c) (hspacing:4/(d:ℝ)≤c):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Color],
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0<Fintype.card V → (Fintype.card V:ℝ)/2≤D → 0<D →
    ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
    0≤β → β≤1/4 → 0<m → m₀≤Fintype.card V →
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Bool Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∀(E:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e,F (f ω))→Prop) (δE:ℝ),
      1-δE≤(μ.sigma (fun ω=>ν (f ω))).probability E→
    1-(δE+failure)≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E z ∧ ∀v,
      ((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
      c*((Q.extendedVertices 1).card:ℝ)) :=by
  obtain ⟨m₀,hm₀,hprob⟩:=raw_expanded_first_vortex_boundary_all_roots_with_event d hd ε ρ₀ failure hε hρ₀ hfailure
  obtain ⟨Nrel,hNrel,hrelative⟩:=first_vortex_all_roots_boundary_relative ε c hε hc
  refine ⟨max m₀ Nrel,by omega,?_⟩
  intro V U Color _ _ _ _ _ G D m β Q hreg hn hD hDpos hρ hρhi hβ hβ1 hm hsize π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν μ f E δE hE
  have hBound:=hprob V U Color G D m β Q hreg hn hD hDpos hρ hρhi hβ hβ1 hm (by omega)
    π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν E δE hE
  have hRel:=hrelative V U G D m β Q (by omega) hreg hDpos hm hρhi d (by omega) hspacing
  apply le_trans hBound
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro v
  exact (hz.2 v).trans hRel
end Oberwolfach
