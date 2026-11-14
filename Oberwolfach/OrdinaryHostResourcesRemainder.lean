module

public import Oberwolfach.OrdinaryDecompositionEdges

@[expose] public section
/-! Removing a typed subhost has the same effect on the unified rim/spoke
resource set, and the removed resources are recovered exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_host_resources_remainder (Q R:SimpleGraph V) (H S:V→U→Prop)
    (hR:R≤Q) (hS:∀v u,S v u→H v u):
    ordinaryHostResources (Q\R) (fun v u=>H v u∧¬S v u)=ordinaryHostResources Q H\ordinaryHostResources R S ∧
    ordinaryHostResources Q H\ordinaryHostResources (Q\R) (fun v u=>H v u∧¬S v u)=ordinaryHostResources R S:=by
  constructor <;> ext e
  all_goals
    cases e with
    | inl edge=>
      induction edge using Sym2.ind with
      | _ v w=>
        simp only [Finset.mem_sdiff,ordinaryHostResources_rim,SimpleGraph.mem_edgeSet,SimpleGraph.sdiff_adj] <;>
          have hh:=fun h=>hR (v:=v) (w:=w) h <;> tauto
    | inr vu=>
      rcases vu with ⟨v,u⟩
      simp only [Finset.mem_sdiff,ordinaryHostResources_spoke] <;> have hh:=hS v u <;> tauto
end Oberwolfach
