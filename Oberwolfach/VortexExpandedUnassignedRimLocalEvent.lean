module

public import Oberwolfach.ExpandedUnassignedRimLocalSmallFailure
public import Oberwolfach.VortexLocalRowSizeConditions

@[expose] public section
/-! Local physical-row tests at all prescribed nonterminal vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_expanded_unassigned_rim_local_common_event
    (ε δ:ℝ) (he:0<ε) (heq:ε≤1/4) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U], ∀(G:SimpleGraph V) (D mv:ℕ) (β:ℝ)
      (Q:Vortex U G D β ε mv) (T:Finset ℕ),
    (m:ℝ)≤ε*mv/2 → (∀i∈T,1 ≤ i ∧ i≤Q.length) →
    ∀ (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∀ (Extra:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ξ:ℝ),
    1-ξ≤(μ.sigma (fun ω=>ν (f ω))).probability Extra →
    1-ξ-δ≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>Extra z ∧ ∀ i∈T,∀ x∈Q.extendedVertices (i-1),
      |(((G.neighborFinset x∩Q.extendedVertices i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩Q.extendedVertices i).card|<((Q.extendedVertices i).card:ℝ)^(3/4:ℝ))    :=by
  obtain ⟨m,hm,hcommon⟩:=raw_expanded_unassigned_rim_local_family_small_failure (2/ε) δ (by positivity) hδ
  refine ⟨m,hm,?_⟩
  intro V U Γ Color _ _ _ _ _ _ G D mv β Q T hterminal hT p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν μ f Extra ξ hExtra
  have hmin:∀i∈T,m≤(Q.extendedVertices i).card:=fun i hi=>
    Q.extended_card_at_least_threshold hterminal (hT i hi).2
  have hpos:∀i∈T,1≤(Q.extendedVertices i).card:=fun i hi=>le_trans hm (hmin i hi)
  have hinj:=Q.extended_card_injOn_positive he.le heq T hpos
  have hB:∀i∈T,((Q.extendedVertices (i-1)).card:ℝ)≤(2/ε)*(Q.extendedVertices i).card:=by
    intro i hi
    exact Q.extended_previous_card_le he (hT i hi).1 (hT i hi).2 (hpos i hi)
  exact hcommon V U Γ Color G ℕ T (fun i=>Q.extendedVertices i) (fun i=>Q.extendedVertices (i-1))
    hmin hinj hB p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν Extra ξ hExtra
end Oberwolfach
