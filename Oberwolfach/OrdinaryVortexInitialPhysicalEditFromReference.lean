module

public import Oberwolfach.OrdinaryForbiddenReferencePhysicalEdit
public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal
public import Oberwolfach.OrdinaryRawPairStateEquality
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Transfer an arbitrary tracked reference edit to the first vortex level,
adding only the explicitly bounded forbidden-edge contribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_physical_edit_from_reference
    (P F G:SimpleGraph V) (Hs:V→U→Prop) (D vsize:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (cost LF:ℝ) (hLF:0≤LF) (hF:∀v,(F.degree v:ℝ)≤LF)
    (hphysical:∀w:V⊕U,((changed
      ((ordinaryPhysicalGraph (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j)).neighborFinset w)
      ((ordinaryPhysicalGraph G Hs).neighborFinset w)).card:ℝ)≤cost):
    let f:markedVortexVertexType Q 0↪V:=(markedVortexVertexEmbedding Q 0).toEmbedding;
    let g:=markedVortexHubEmbedding Q 0;let ρ:=markedVortexPermutation Q π hπ 0;
    let raw:=ordinaryRawRestrictPair f g σ;
    ∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤cost+LF :=by
  intro f g ρ raw
  let R:=rawWheelGraph P σ
  let J:=rawWheelSpokes π d σ j
  have hglobal:=ordinary_forbidden_reference_physical_edit R F G J Hs cost LF hLF hF hphysical
  have hlocal:=ordinary_induced_physical_edit_of_global R G J Hs (Q.extendedVertices 0) (Q.extendedIndices 0)
    (cost+LF) hglobal
  have hgraph:rawWheelGraph (P.comap f) raw=R.induce ((Q.extendedVertices 0):Set V):=by
    exact ordinary_raw_pair_graph_eq f g P σ
  have hcomm:∀x,f (ρ x)=π (f x):=(marked_vortex_permutation_compatibility Q π hπ 0).1
  have hspoke:rawWheelSpokes ρ d raw j=fun v u=>J (f v) (g u):=by
    convert ordinary_raw_pair_spokes_eq f g π ρ hcomm d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  intro w
  have hh:=hlocal w
  rw [hgraph,hspoke]
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
