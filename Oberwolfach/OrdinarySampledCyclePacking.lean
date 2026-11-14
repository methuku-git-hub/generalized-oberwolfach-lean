module

public import Oberwolfach.OrdinaryCycleSampledHypergraph
public import Oberwolfach.CycleHypergraphNearPerfect

@[expose] public section
/-! The matching conclusion for the actual retained ordinary cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampled_cycle_packing
    (r B:ℕ) (hr:3≤r) (K a γ ε:ℝ) (hK:0<K) (ha:0<a)
    (hγ:0<γ) (hγ1:γ≤1) (hε:0≤ε) (hmargin:a*r≤1-ε):
    ∃ n₀:ℕ,∀ n D:ℕ,n₀≤n→n≤D→D≤n^B→
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V)
      [DecidableEq (OrdinaryCycle G r)] (σ:OrdinaryCycle G r→Bool),
    n≤Fintype.card V→Fintype.card V≤n^B→
    (∀ v,(1-ε)*D ≤ independentCycleCount (fun C=>v∈C.val.val.support) σ ∧
       independentCycleCount (fun C=>v∈C.val.val.support) σ≤D)→
    (∀ u v,u≠v→independentCycleCount (fun C=>u∈C.val.val.support ∧ v∈C.val.val.support) σ≤K*D/n)→
    ∃ M:Finset (RetainedOrdinaryCycle G r σ),
      (∀ C∈M,∀ C'∈M,C≠C'→Disjoint (retainedOrdinaryCycleVertices C) (retainedOrdinaryCycleVertices C')) ∧
      (1-γ)*(1-ε)*Fintype.card V≤(r:ℝ)*M.card := by
  obtain ⟨N,hN⟩:=cycle_hypergraph_near_perfect r B (by omega) K a γ ε hK ha hγ hγ1 hε hmargin
  refine ⟨N,?_⟩
  intro n D hn hnD hDB V _ _ G _ σ hnV hV hdegrees hcodeg
  apply hN n D hn hnD hDB V (RetainedOrdinaryCycle G r σ)
    (retainedOrdinaryCycleVertices (G:=G) (r:=r) (σ:=σ)) hnV hV
    (fun C=>retained_ordinary_cycle_vertices_card C)
  · intro v
    constructor
    · rw [retained_ordinary_cycle_degree]
      exact (hdegrees v).1
    · have hh: (Fintype.card (HypergraphEdgesAt
        (retainedOrdinaryCycleVertices (G:=G) (r:=r) (σ:=σ)) v):ℝ)≤D:=by
          rw [retained_ordinary_cycle_degree];exact (hdegrees v).2
      exact_mod_cast hh
  · intro u v huv
    rw [retained_ordinary_cycle_codegree]
    exact hcodeg u v huv
end Oberwolfach
