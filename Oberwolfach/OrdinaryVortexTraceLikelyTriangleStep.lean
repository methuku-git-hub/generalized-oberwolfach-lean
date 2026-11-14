module

public import Oberwolfach.OrdinaryVortexTraceLocalCoverdown
public import Oberwolfach.OrdinaryTriangleLikelyEventCoverdown

@[expose] public section
/-! A sufficiently likely local triangle event supplies an ambient
    protected vortex-trace step with the stated budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_likely_triangle_step
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (S F:SimpleGraph V) (H:V→U→Prop) (cost deepCost:ℕ→ℝ)
    (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (hc0:0≤cost (i+1)) (hd0:0≤deepCost (i+1)):
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2)
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let Vloc:=markedVortexVertexType Q (i+1);let Uloc:=markedVortexHubType Q (i+1)
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    ∀(μ:FiniteLaw (Sym2 (Vloc⊕Uloc)→Bool)) (E:(Sym2 (Vloc⊕Uloc)→Bool)→Prop)
      (loss localCost rate:ℝ),
    16≤Fintype.card Vloc→loss≤1/4→
    1-(loss+2/(Fintype.card (Vloc⊕Uloc):ℝ))-
      (1/(Fintype.card Vloc:ℝ)+1/(Fintype.card (Vloc⊕Uloc):ℝ))≤μ.probability E→
    (∀σ,E σ→OrdinaryProtectedHostCoverDownResult (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      (markedVortexInnerVertices Q (i+1)) (markedVortexDeeperVertices Q (i+1))
      (markedVortexInnerHubs Q (i+1)) (markedVortexDeeperHubs Q (i+1)) 3 localCost localCost)→
    localCost≤rate*Fintype.card (Vloc⊕Uloc)→ rate*Fintype.card (Vloc⊕Uloc)≤cost (i+1)→
    rate*Fintype.card (Vloc⊕Uloc)≤deepCost (i+1)→
    OrdinaryProtectedHostCoverDownResult G F Hs (X (i+1)) (T (i+1)) (Z (i+1)) (W (i+1)) 3
      (cost (i+1)) (deepCost (i+1)) :=by
  intro X T Z W f g Vloc Uloc htrace hstate hbal hdiv μ E loss localCost rate hn hloss hprob hevent hlocal hcost hdeep
  have hlocal':=ordinary_triangle_coverdown_of_likely_event (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) (markedVortexInnerVertices Q (i+1)) (markedVortexDeeperVertices Q (i+1))
    (markedVortexInnerHubs Q (i+1)) (markedVortexDeeperHubs Q (i+1)) μ E loss localCost rate hn hloss hprob hevent hlocal
  have hlocal'':=ordinary_protected_cover_down_cost_mono (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) (markedVortexInnerVertices Q (i+1)) (markedVortexDeeperVertices Q (i+1))
    (markedVortexInnerHubs Q (i+1)) (markedVortexDeeperHubs Q (i+1)) 3
    (rate*Fintype.card (Vloc⊕Uloc)) (rate*Fintype.card (Vloc⊕Uloc)) (cost (i+1)) (deepCost (i+1)) hcost hdeep hlocal'
  exact ordinary_vortex_trace_local_coverdown P D m β ε Q S F H cost deepCost i 3 A G Hs hc0 hd0 htrace hstate hbal hdiv hlocal''
end Oberwolfach
