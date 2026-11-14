module

public import Oberwolfach.MarkedReferenceActiveAbsorberProperty
public import Oberwolfach.MarkedEmptyPhysicalDeletion
public import Oberwolfach.GraphBottomEdgeFinsetAnyInstance

@[expose] public section
/-! Take zero deletions in the common active-neighbourhood event, retaining
the original inner-minus-deeper vertex and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_reference_active_endpoint_base
    (r h d:ℕ) (α βconfig εref δref tol ζActive ζAbs tstar εAbs:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hevent:MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let A:=markedVortexInnerVertices Q i\markedVortexDeeperVertices Q i
      let B:=markedVortexInnerHubs Q i\markedVortexDeeperHubs Q i
      let ω:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u);
      MarkedRowsWithSpokes (G.comap f) ρ d h A p k (fun u=>q (g u)) (fun u=>s (g u)) a j
        ((tol+h*ζActive)*A.card) ω H ∧
      MarkedIndicesWithSpokes ρ d h B (fun u=>q (g u)) (fun u=>s (g u)) a j
        ((tol+h*ζActive)*B.card) ω H:=by
  intro i hi W Z f g ρ A B ω H
  have hh:=hevent.1.2 i hi 0 0 0 (by norm_num) (by norm_num) (by norm_num)
    (⊥:SimpleGraph W) (⊥:SimpleGraph (W⊕Z))
    (by intro x;simp) (by intro x;simp) (by intro u;simp)
  simpa only [graph_bottom_edgeFinset_any_instance,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom,
    mul_zero,add_zero] using hh
end Oberwolfach
