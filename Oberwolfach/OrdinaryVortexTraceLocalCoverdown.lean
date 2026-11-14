module

public import Oberwolfach.OrdinaryTraceInducedCoverDown
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Lift a cover-down on the actual marked-vortex parent to the ambient
    protected trace, preserving both cost budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_local_coverdown
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (S F:SimpleGraph V) (H:V→U→Prop) (cost deepCost:ℕ→ℝ)
    (i r:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (hc0:0≤cost (i+1)) (hd0:0≤deepCost (i+1)):
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2)
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryProtectedHostCoverDownResult (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      (markedVortexInnerVertices Q (i+1)) (markedVortexDeeperVertices Q (i+1))
      (markedVortexInnerHubs Q (i+1)) (markedVortexDeeperHubs Q (i+1)) r (cost (i+1)) (deepCost (i+1))→
    OrdinaryProtectedHostCoverDownResult G F Hs (X (i+1)) (T (i+1)) (Z (i+1)) (W (i+1)) r
      (cost (i+1)) (deepCost (i+1)) :=by
  intro X T Z W f g htrace hstate hbal hdiv hlocal
  have hparent:ordinaryHostResources G Hs⊆ordinaryRootResources (X i) (Z i):=by
    rw [hstate]
    have hh:=ordinary_protected_trace_terminal S H X T Z W cost deepCost (i+1) (by omega) A htrace
    simpa only [Nat.add_sub_cancel] using hh
  have hh:=ordinary_induced_protected_coverdown G F Hs (X i) (Z i)
    (markedVortexInnerVertices Q (i+1)) (markedVortexDeeperVertices Q (i+1))
    (markedVortexInnerHubs Q (i+1)) (markedVortexDeeperHubs Q (i+1)) r
    (cost (i+1)) (deepCost (i+1)) hc0 hd0 hparent hbal hdiv hlocal
  obtain ⟨hx,ht,hz,hw⟩:=marked_vortex_inner_images Q (i+1)
  change (markedVortexInnerVertices Q (i+1)).image (Subtype.val:markedVortexVertexType Q (i+1)→V)=X (i+1) at hx
  change (markedVortexDeeperVertices Q (i+1)).image (Subtype.val:markedVortexVertexType Q (i+1)→V)=T (i+1) at ht
  change (markedVortexInnerHubs Q (i+1)).image (Subtype.val:markedVortexHubType Q (i+1)→U)=Z (i+1) at hz
  change (markedVortexDeeperHubs Q (i+1)).image (Subtype.val:markedVortexHubType Q (i+1)→U)=W (i+1) at hw
  simp only [Function.Embedding.coeFn_mk] at hh
  rw [hx,ht,hz,hw] at hh
  exact hh
end Oberwolfach
