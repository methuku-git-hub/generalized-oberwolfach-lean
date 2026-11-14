module

public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal
public import Oberwolfach.OrdinaryRawPairStateEquality
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Restrict a global sample-to-actual-host physical edit bound to any vortex
level, using the very same raw sample and permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_sample_physical_edit_of_global
    (P G:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (i:ℕ) (L:ℝ)
    (hglobal:∀w:V⊕U,((changed ((ordinaryPhysicalGraph (rawWheelGraph P σ) (rawWheelSpokes π d σ j)).neighborFinset w)
      ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ)≤L):
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ i;let raw:=ordinaryRawRestrictPair f g σ;
    ∀a:markedVortexVertexType Q i⊕markedVortexHubType Q i,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset a)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>H (f v) (g u))).neighborFinset a)).card:ℝ)≤L :=by
  intro f g ρ raw
  have hlocal:=ordinary_induced_physical_edit_of_global (rawWheelGraph P σ) G (rawWheelSpokes π d σ j) H
    (Q.extendedVertices i) (Q.extendedIndices i) L hglobal
  have hrim:rawWheelGraph (P.comap f) raw=(rawWheelGraph P σ).induce ((Q.extendedVertices i):Set V):=by
    exact ordinary_raw_pair_graph_eq f.toEmbedding g P σ
  have hspoke:rawWheelSpokes ρ d raw j=fun (v:↥(Q.extendedVertices i)) (u:↥(Q.extendedIndices i))=>
      rawWheelSpokes π d σ j v.val u.val:=by
    convert ordinary_raw_pair_spokes_eq f.toEmbedding g π ρ (by intro x;rfl) d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  intro a
  rw [hrim,hspoke]
  have hh:=hlocal a
  convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
