module

public import Oberwolfach.ComponentFamilyDomainCard
public import Oberwolfach.LongAssignedClassReservation
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! Long component sizes sum to the actual long-class vertex count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_component_totals_any_class
    {n K:ℕ} {U:Type} [Fintype U] (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (w:U):
    let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
    let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _
    (∀i, K+1≤Fintype.card (components i)) ∧
    ((∑i:I,Fintype.card (components i):ℕ):ℝ)=ordinaryAssignedFraction F hF K w none*n:=by
  intro I components
  have hmem:∀v:Fin n,(∃i:I,v∈(components i).supp) ↔ K<Fintype.card ((F w).connectedComponentMk v):=by
    intro v
    constructor
    · rintro ⟨i,hi⟩
      change (F w).connectedComponentMk v=i.val at hi
      rw [hi]
      exact i.property
    · intro hv
      exact ⟨⟨(F w).connectedComponentMk v,hv⟩,rfl⟩
  have hc:=component_family_domain_card (F w) components components.injective
  have heq:(Finset.univ.filter (fun v:Fin n=>longPreparationCycleClass (F w) (hF w) K v=none)).card=
      ∑i:I,Fintype.card (components i):=by
    rw [←hc,Fintype.card_subtype]
    congr 1
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ((long_preparation_cycle_class (F w) (hF w) K v).1).trans (hmem v).symm
  refine ⟨?_,?_⟩
  · intro i
    exact Nat.succ_le_iff.mpr i.property
  · unfold ordinaryAssignedFraction
    rw [heq]
    have hnR:(n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
end Oberwolfach
