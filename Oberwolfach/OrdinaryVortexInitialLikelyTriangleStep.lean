module

public import Oberwolfach.OrdinaryVortexInitialLocalCoverdown
public import Oberwolfach.OrdinaryTriangleLikelyEventCoverdown

@[expose] public section
/-! A sufficiently likely first-level triangle event yields the initial
    ambient protected cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_likely_triangle_step
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (G F:SimpleGraph V) (Hs:V→U→Prop) (cost deepCost:ℝ)
    (hc0:0≤cost) (hd0:0≤deepCost)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card):
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0
    let Vloc:=markedVortexVertexType Q 0;let Uloc:=markedVortexHubType Q 0
    ∀(μ:FiniteLaw (Sym2 (Vloc⊕Uloc)→Bool)) (E:(Sym2 (Vloc⊕Uloc)→Bool)→Prop)
      (loss localCost rate:ℝ),
    16≤Fintype.card Vloc→loss≤1/4→
    1-(loss+2/(Fintype.card (Vloc⊕Uloc):ℝ))-
      (1/(Fintype.card Vloc:ℝ)+1/(Fintype.card (Vloc⊕Uloc):ℝ))≤μ.probability E→
    (∀σ,E σ→OrdinaryProtectedHostCoverDownResult (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      (markedVortexInnerVertices Q 0) (markedVortexDeeperVertices Q 0)
      (markedVortexInnerHubs Q 0) (markedVortexDeeperHubs Q 0) 3 localCost localCost)→
    localCost≤rate*Fintype.card (Vloc⊕Uloc)→ rate*Fintype.card (Vloc⊕Uloc)≤cost→
    rate*Fintype.card (Vloc⊕Uloc)≤deepCost→
    OrdinaryProtectedHostCoverDownResult G F Hs (Q.extendedVertices 1) (Q.extendedVertices 2)
      (Q.extendedIndices 1) (Q.extendedIndices 2) 3 cost deepCost :=by
  intro f g Vloc Uloc μ E loss localCost rate hn hloss hprob hevent hlocal hcost hdeep
  have hlocal':=ordinary_triangle_coverdown_of_likely_event (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) (markedVortexInnerVertices Q 0) (markedVortexDeeperVertices Q 0)
    (markedVortexInnerHubs Q 0) (markedVortexDeeperHubs Q 0) μ E loss localCost rate hn hloss hprob hevent hlocal
  have hlocal'':=ordinary_protected_cover_down_cost_mono (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) (markedVortexInnerVertices Q 0) (markedVortexDeeperVertices Q 0)
    (markedVortexInnerHubs Q 0) (markedVortexDeeperHubs Q 0) 3
    (rate*Fintype.card (Vloc⊕Uloc)) (rate*Fintype.card (Vloc⊕Uloc)) cost deepCost hcost hdeep hlocal'
  exact ordinary_vortex_initial_local_coverdown P D m β ε Q G F Hs 3 cost deepCost hc0 hd0 hbal hdiv hlocal''
end Oberwolfach
