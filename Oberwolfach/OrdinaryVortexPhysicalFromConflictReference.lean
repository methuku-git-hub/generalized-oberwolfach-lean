module

public import Oberwolfach.OrdinaryPhysicalEditPrependConflict
public import Oberwolfach.OrdinaryVortexSamplePhysicalEditOfGlobal

@[expose] public section
/-! A global actual-host edit from the conflict-deleted sample supplies the
local raw-sample edit needed at every vortex level, including the initial one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_physical_from_conflict_reference
    (P F G:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (i:ℕ) (LF L:ℝ)
    (hLF:0≤LF) (hF:∀v,(F.degree v:ℝ)≤LF)
    (hreference:∀w:V⊕U,((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ)\F)
      (rawWheelSpokes π d σ j)).neighborFinset w) ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ)≤L):
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ i;let raw:=ordinaryRawRestrictPair f g σ;
    ∀a:markedVortexVertexType Q i⊕markedVortexHubType Q i,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset a)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>H (f v) (g u))).neighborFinset a)).card:ℝ)≤LF+L :=by
  have hglobal:=ordinary_physical_edit_prepend_conflict (rawWheelGraph P σ) F G (rawWheelSpokes π d σ j) H LF L hLF hF hreference
  exact ordinary_vortex_sample_physical_edit_of_global P G H D m β ε Q π hπ d j σ i (LF+L) hglobal
end Oberwolfach
