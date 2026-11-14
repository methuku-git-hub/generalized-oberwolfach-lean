module

public import Oberwolfach.ExpandedUnassignedHubLocalSmallFailure
public import Oberwolfach.VortexLocalRowSizeConditions
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! Unassigned-spoke rows at every sufficiently large vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_expanded_unassigned_hub_local_common_event
    (d:ℕ) (hd:2≤d) (ε δ:ℝ) (he:0<ε) (heq:ε≤1/4) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(V U Γ Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Γ] [Fintype Color], ∀(G:SimpleGraph V) (D mv:ℕ) (β:ℝ)
      (Q:Vortex U G D β ε mv) (T:Finset ℕ),
    (m:ℝ)≤ε*mv/2 → (∀i∈T,1 ≤ i ∧ i≤Q.length) →
    G.IsRegularOfDegree D → 0<Fintype.card V → 0<D → initialIndexDensity U D≤1 →
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀i∈T,∀w∈Q.extendedIndices i,
      |rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Q.extendedVertices i)-
      ((Q.extendedVertices i).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((Q.extendedVertices i).card:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨m,hm,hcommon⟩:=raw_expanded_unassigned_hub_local_family_small_failure d hd (1/2) δ (by norm_num) hδ
  refine ⟨m,hm,?_⟩
  intro V U Γ Color _ _ _ _ _ _ G D mv β Q T hterminal hT hreg hn hD hρ π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν μ f
  have hmin:∀i∈T,m≤(Q.extendedVertices i).card:=fun i hi=>
    Q.extended_card_at_least_threshold hterminal (hT i hi).2
  have hpos:∀i∈T,1≤(Q.extendedVertices i).card:=fun i hi=>le_trans hm (hmin i hi)
  have hinj:=Q.extended_card_injOn_positive he.le heq T hpos
  have hB:∀i∈T,((Q.extendedIndices i).card:ℝ)≤(1/2:ℝ)*(Q.extendedVertices i).card:=by
    intro i hi
    have hh:=Q.extended_index_size_upper hreg hn hD he.le hρ i
    have hhR:(2:ℝ)*(Q.extendedIndices i).card≤(Q.extendedVertices i).card:=by exact_mod_cast hh
    linarith only [hhR]
  exact hcommon V U Γ Color ℕ T (fun i=>Q.extendedVertices i) (fun i=>Q.extendedIndices i)
    hmin hinj hB π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
end Oberwolfach
