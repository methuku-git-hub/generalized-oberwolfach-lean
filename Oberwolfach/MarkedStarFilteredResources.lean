module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Star-filtering the marked arcs and spoke pairs keeps only physical
resources incident with the removed star. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_star_filtered_resources
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (T:Finset V) (W:Finset U)
    (hT:∀ x,π x∈T↔x∈T):
    ∀ e∈markedFiniteResources tail head ktail khead π
      (A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
      (S.filter (fun z=>z.1∈T∨z.2∈W)),markedStarResource T W e:=by
  intro e he
  rw [markedFiniteResources_star tail head ktail khead π A S T W hT] at he
  exact (Finset.mem_filter.mp he).2
end Oberwolfach
