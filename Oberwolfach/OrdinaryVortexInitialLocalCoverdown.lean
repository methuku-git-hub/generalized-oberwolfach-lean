module

public import Oberwolfach.OrdinaryInducedProtectedCoverDown
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Lift the first marked-vortex cover-down to the entire original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_local_coverdown
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (G F:SimpleGraph V) (Hs:V→U→Prop) (r:ℕ) (cost deepCost:ℝ)
    (hc0:0≤cost) (hd0:0≤deepCost)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card):
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    OrdinaryProtectedHostCoverDownResult (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      (markedVortexInnerVertices Q 0) (markedVortexDeeperVertices Q 0)
      (markedVortexInnerHubs Q 0) (markedVortexDeeperHubs Q 0) r cost deepCost→
    OrdinaryProtectedHostCoverDownResult G F Hs (Q.extendedVertices 1) (Q.extendedVertices 2)
      (Q.extendedIndices 1) (Q.extendedIndices 2) r cost deepCost :=by
  intro f g hlocal
  have hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices 0) (Q.extendedIndices 0):=by
    apply ordinaryRootResources_contains
    · intro v hv
      rw [Q.extendedVertices_eq (Nat.zero_le _),Q.initial]
      exact Finset.mem_univ v
    · intro u hu
      rw [Q.extendedIndices_eq (Nat.zero_le _),Q.indices_initial]
      exact Finset.mem_univ u
  have hh:=ordinary_induced_protected_coverdown G F Hs (Q.extendedVertices 0) (Q.extendedIndices 0)
    (markedVortexInnerVertices Q 0) (markedVortexDeeperVertices Q 0)
    (markedVortexInnerHubs Q 0) (markedVortexDeeperHubs Q 0) r cost deepCost hc0 hd0 hsupport hbal hdiv hlocal
  obtain ⟨hx,ht,hz,hw⟩:=marked_vortex_inner_images Q 0
  simp only [Function.Embedding.coeFn_mk] at hh
  change (markedVortexInnerVertices Q 0).image (Subtype.val:markedVortexVertexType Q 0→V)=Q.extendedVertices 1 at hx
  change (markedVortexDeeperVertices Q 0).image (Subtype.val:markedVortexVertexType Q 0→V)=Q.extendedVertices 2 at ht
  change (markedVortexInnerHubs Q 0).image (Subtype.val:markedVortexHubType Q 0→U)=Q.extendedIndices 1 at hz
  change (markedVortexDeeperHubs Q 0).image (Subtype.val:markedVortexHubType Q 0→U)=Q.extendedIndices 2 at hw
  rw [hx,ht,hz,hw] at hh
  exact hh
end Oberwolfach
