module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.BipartiteBlockMatching

@[expose] public section

/-! Exact conversion between physical bipartite graph counts and the
row-hub relation. Sampled endpoint classes keep their original labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem physical_bipartite_row_count (H:V→U→Prop) (D:SimpleGraph (V⊕U)) (B:Finset U) (v:V) :
    ((B.image Sum.inr)∩((ordinaryPhysicalGraph ⊥ H)\D).neighborFinset (Sum.inl v)).card=
      (B.filter (fun u=>H v u∧¬D.Adj (Sum.inl v) (Sum.inr u))).card := by
  have he : (B.image Sum.inr)∩((ordinaryPhysicalGraph ⊥ H)\D).neighborFinset (Sum.inl v)=
      (B.filter (fun u=>H v u∧¬D.Adj (Sum.inl v) (Sum.inr u))).image Sum.inr := by
    ext z
    cases z <;> simp [ordinaryPhysicalGraph]
  rw [he,Finset.card_image_of_injective _ Sum.inr_injective]

theorem physical_bipartite_col_count (H:V→U→Prop) (D:SimpleGraph (V⊕U)) (A:Finset V) (u:U) :
    ((A.image Sum.inl)∩((ordinaryPhysicalGraph ⊥ H)\D).neighborFinset (Sum.inr u)).card=
      (A.filter (fun v=>H v u∧¬D.Adj (Sum.inl v) (Sum.inr u))).card := by
  have he : (A.image Sum.inl)∩((ordinaryPhysicalGraph ⊥ H)\D).neighborFinset (Sum.inr u)=
      (A.filter (fun v=>H v u∧¬D.Adj (Sum.inl v) (Sum.inr u))).image Sum.inl := by
    ext z
    cases z <;> simp [ordinaryPhysicalGraph,SimpleGraph.adj_comm D]
  rw [he,Finset.card_image_of_injective _ Sum.inl_injective]

theorem physical_bipartite_cut_count (H:V→U→Prop) (D:SimpleGraph (V⊕U)) (S:Finset V) (T:Finset U) :
    bipartiteMatrixCut (fun z w=>if ((ordinaryPhysicalGraph ⊥ H)\D).Adj z w then 1 else 0)
      (S.image Sum.inl) (T.image Sum.inr)=
    bipartiteMatrixCut (fun v u=>if H v u∧¬D.Adj (Sum.inl v) (Sum.inr u) then 1 else 0) S T := by
  simp only [bipartiteMatrixCut,Finset.sum_image,Sum.inl_injective.injOn,Sum.inr_injective.injOn]
  rfl

theorem physical_bipartite_codegree_count (H:V→U→Prop) (B:Finset U) (v w:V) :
    (((B.image Sum.inr)∩(ordinaryPhysicalGraph ⊥ H).neighborFinset (Sum.inl v))∩
      (ordinaryPhysicalGraph ⊥ H).neighborFinset (Sum.inl w)).card=
    (B.filter (fun u=>H v u∧H w u)).card := by
  have he : ((B.image Sum.inr)∩(ordinaryPhysicalGraph ⊥ H).neighborFinset (Sum.inl v))∩
      (ordinaryPhysicalGraph ⊥ H).neighborFinset (Sum.inl w)=
      (B.filter (fun u=>H v u∧H w u)).image Sum.inr := by
    ext z
    cases z <;> simp [ordinaryPhysicalGraph,and_assoc]
  rw [he,Finset.card_image_of_injective _ Sum.inr_injective]


theorem physical_bipartite_block_from_counts (H:V→U→Prop) (D:SimpleGraph (V⊕U))
    (A:Finset V) (B:Finset U) (d tau lam:ℝ)
    (hr:∀ v∈A,d≤(((B.image Sum.inr)∩((ordinaryPhysicalGraph ⊥ H)\D).neighborFinset (Sum.inl v)).card:ℝ))
    (hc:∀ u∈B,d≤(((A.image Sum.inl)∩((ordinaryPhysicalGraph ⊥ H)\D).neighborFinset (Sum.inr u)).card:ℝ))
    (hcut:∀ S⊆A.image Sum.inl,∀ T⊆B.image Sum.inr,tau≤(S.card:ℝ)→tau≤(T.card:ℝ)→
      lam*S.card*T.card≤(bipartiteMatrixCut (fun z w=>if ((ordinaryPhysicalGraph ⊥ H)\D).Adj z w then 1 else 0) S T:ℝ)) :
    BipartiteBlockBounds (fun v u=>H v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
      (fun v=>v∈A) (fun u=>u∈B) d tau lam := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    have hh:=hr v hv
    rw [physical_bipartite_row_count] at hh
    convert hh using 1
    congr 2
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  · intro u hu
    have hh:=hc u hu
    rw [physical_bipartite_col_count] at hh
    convert hh using 1
    congr 2
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  · intro S T hS hT hs ht
    have hh:=hcut (S.image Sum.inl) (Finset.image_subset_image hS)
      (T.image Sum.inr) (Finset.image_subset_image hT)
      (by simpa only [Finset.card_image_of_injective _ Sum.inl_injective] using hs)
      (by simpa only [Finset.card_image_of_injective _ Sum.inr_injective] using ht)
    simp only [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,physical_bipartite_cut_count] at hh
    convert hh using 1 <;> congr!

end Oberwolfach
