module

public import Oberwolfach.AmbientSubset
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Embed a fixed-size set of an induced graph in the ambient graph,
retaining its cardinality, degree counts, and conflict-free property. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def inducedSetEmbedding (B : Finset V) {k : ℕ} (S : FixedSubset {v // v∈B} k) : FixedSubset V k :=
  ⟨S.val.map (Function.Embedding.subtype _),by rw [Finset.card_map,S.property]⟩

theorem inducedSetEmbedding_injective (B : Finset V) (k : ℕ) :
    Function.Injective (inducedSetEmbedding B (k:=k)) := by
  intro S T h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact Finset.map_injective (Function.Embedding.subtype _) hh


theorem inducedSetEmbedding_subset (B : Finset V) {k : ℕ} (S : FixedSubset {v // v∈B} k) :
    (inducedSetEmbedding B S).val⊆B := subtype_sample_subset B S.val


theorem inducedSetEmbedding_degree (P : SimpleGraph V) (B : Finset V) {k : ℕ}
    (S : FixedSubset {v // v∈B} k) (v : {v // v∈B}) :
    (((P.induce (B:Set V)).neighborFinset v)∩S.val).card=
      (P.neighborFinset v.val∩(inducedSetEmbedding B S).val).card := by
  have he : (P.induce (B:Set V)).neighborFinset v=(P.neighborFinset v.val).subtype (fun x=>x∈B) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj,Finset.mem_subtype]
  rw [he]
  convert subtype_sample_intersection_card (P.neighborFinset v.val) B S.val using 1 <;> congr!


theorem inducedSetEmbedding_conflict_free (F : SimpleGraph V) (B : Finset V) {k : ℕ}
    (S : FixedSubset {v // v∈B} k)
    (h : ∀ x∈S.val,∀ y∈S.val,¬(F.induce (B:Set V)).Adj x y) :
    ∀ x∈(inducedSetEmbedding B S).val,∀ y∈(inducedSetEmbedding B S).val,¬F.Adj x y := by
  intro x hx y hy hxy
  obtain ⟨x',hx',rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨y',hy',rfl⟩ := Finset.mem_map.mp hy
  exact h x' hx' y' hy' hxy


theorem induced_degree_le_ambient (F : SimpleGraph V) (B : Finset V) (v : {v // v∈B}) :
    (F.induce (B:Set V)).degree v≤F.degree v.val := by
  rw [induced_degree_intersection,← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

end Oberwolfach
