module

public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.PhysicalEdgeGraph

@[expose] public section

/-! Physical rim edges of a finite resource set, and their avoidance of an
already deleted correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedResourceRimEdges (C : Finset (Finset V ⊕ (V × U))) : Finset (Finset V) :=
  Finset.univ.filter (fun e => Sum.inl e ∈ C)

def markedResourceRimGraph (C : Finset (Finset V ⊕ (V × U))) : SimpleGraph V :=
  physicalEdgeGraph (markedResourceRimEdges C)

theorem markedResourceRimGraph_degree_le (C : Finset (Finset V ⊕ (V × U))) (v : V) :
    (markedResourceRimGraph C).degree v ≤ C.card := by
  have hc : (markedResourceRimEdges C).card ≤ C.card := by
    let f : {e // e ∈ markedResourceRimEdges C} → {x // x ∈ C} :=
      fun e => ⟨Sum.inl e.val, (Finset.mem_filter.mp e.property).2⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact Sum.inl.inj (congrArg Subtype.val h)
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe] using h
  exact (physicalEdgeGraph_degree_le_incident (markedResourceRimEdges C) v).trans
    ((Finset.card_filter_le _ _).trans hc)

theorem markedReferenceDeletion_disjoint_resourceRimGraph
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (D : MarkedReferenceDeletion P π d σ)
    (C : Finset (Finset V ⊕ (V × U))) (hdis : Disjoint D.removed C) :
    ∀ x y, (markedSampleArcSetGraph P π d σ D.arcs).Adj x y →
      ¬ (markedResourceRimGraph C).Adj x y := by
  intro x y hxy hC
  have hmem : Sum.inl ({x,y} : Finset V) ∈ D.removed := by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxy.2
    unfold MarkedReferenceDeletion.removed markedFiniteResources
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨a,ha,congrArg Sum.inl he⟩
  have hCmem : Sum.inl ({x,y} : Finset V) ∈ C :=
    (Finset.mem_filter.mp hC.2).2
  exact (Finset.disjoint_left.mp hdis) hmem hCmem
end Oberwolfach
