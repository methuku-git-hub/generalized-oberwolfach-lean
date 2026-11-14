module

public import Oberwolfach.ResidualActualEmbeddingOverlap
public import Oberwolfach.ResidualSubtypeIndependent

@[expose] public section
/-! Supply the overlap and restricted-injection hypotheses of the gluing
lemma from the actual equality between old and residual domains. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [DecidableEq V] [DecidableEq W]

theorem residual_subtype_glue_inputs (R A X:Finset V) (hX:X∩R=A) (ψ:V→W)
    (hψ:Set.InjOn ψ (↑X:Set V)):
    (∀x:{x // x∈R},x∈residualSubtypeSet R A ↔ x.1∈X) ∧
    Set.InjOn (fun x:{x // x∈R}=>ψ x.1) (↑(residualSubtypeSet R A):Set {x // x∈R}) := by
  have hequiv:∀x:{x // x∈R},x∈residualSubtypeSet R A ↔ x.1∈X:=by
    intro x
    simp only [residualSubtypeSet,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←hX,Finset.mem_inter]
    exact ⟨And.left,fun hx=>⟨hx,x.2⟩⟩
  refine ⟨hequiv,?_⟩
  · intro x hx y hy hxy
    exact Subtype.ext (hψ ((hequiv x).1 hx) ((hequiv y).1 hy) hxy)
end Oberwolfach
