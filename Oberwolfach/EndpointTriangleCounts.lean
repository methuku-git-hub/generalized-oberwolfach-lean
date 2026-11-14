module

public import Oberwolfach.ClassSparseGreedySequences
public import Oberwolfach.EndpointTriangles

@[expose] public section

/-! Explicit row and index common-neighbourhood hypotheses for the endpoint
triangle construction. Indices are required to meet two row roots only when
that pair is nonconflicting. No condition is imposed on a pair of prescribed
roots belonging to different replacement triangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

structure EndpointNeighbourCounts (Q F : SimpleGraph V) (S T : Finset V) (b : ℝ) : Prop where
  indices : b≤(T.card:ℝ)
  rows : ∀ Y J : Finset V,Y⊆S → J⊆T → Y.card≤2 → J.card≤2 → Y.card+J.card≤3 →
    b≤((common S (Y∪J) (fun v=>Q.neighborFinset v)).card:ℝ)
  pairs : ∀ v∈S,∀ w∈S,v≠w → ¬F.Adj v w →
    b≤((common T {v,w} (fun z=>Q.neighborFinset z)).card:ℝ)

def endpointBaseClass (S T : Finset V) (n : ℕ) : Finset V := if n=0 then T else S

def allPreviousLabels (n : ℕ) (f : Fin n→V) : Finset V := Finset.univ.image f

theorem allPreviousGood_adj (Q F : SimpleGraph V) (A : ℕ→Finset V) (W : Finset V)
    {n : ℕ} (f : Fin n→V) (hf : ClassSparseGreedyGood Q F A W allPreviousLabels f)
    (i j : Fin n) (hne : i≠j) : Q.Adj (f i) (f j) := by
  have hordered (i j : Fin n) (hij : i.val<j.val) : Q.Adj (f i) (f j) := by
    apply hf.2.2.2.2 j
    exact Finset.mem_image.mpr ⟨⟨i.val,hij⟩,Finset.mem_univ _,rfl⟩
  rcases lt_or_gt_of_ne (show i.val≠j.val from fun h=>hne (Fin.ext h)) with h|h
  · exact hordered i j h
  · exact (hordered j i h).symm

theorem endpoint_base_common (Q F : SimpleGraph V) (S T W : Finset V)
    (hST : Disjoint S T) (b : ℝ) (hb : EndpointNeighbourCounts Q F S T b)
    (n : ℕ) (hn : n<3) (f : Fin n→V)
    (hf : ClassSparseGreedyGood Q F (endpointBaseClass S T) W allPreviousLabels f) :
    b≤((common (endpointBaseClass S T n) (allPreviousLabels n f) (fun v=>Q.neighborFinset v)).card:ℝ) := by
  by_cases hn0 : n=0
  · subst n
    simpa [allPreviousLabels,endpointBaseClass,common] using hb.indices
  let X := allPreviousLabels n f
  have hX : X⊆S∪T := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    have hi := (hf.2.1 i).1
    by_cases h : i.val=0
    · exact Finset.mem_union_right _ (by simpa only [endpointBaseClass,if_pos h] using hi)
    · exact Finset.mem_union_left _ (by simpa only [endpointBaseClass,if_neg h] using hi)
  have he : (X∩S)∪(X∩T)=X := by
    ext v;simp only [Finset.mem_inter,Finset.mem_union]
    constructor
    · tauto
    · intro hv;exact (Finset.mem_union.mp (hX hv)).elim (fun h=>Or.inl ⟨hv,h⟩) (fun h=>Or.inr ⟨hv,h⟩)
  have hc : X.card≤2 := (Finset.card_image_le.trans_eq (Fintype.card_fin n)).trans (by omega)
  have hs : (X∩S).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans hc
  have ht : (X∩T).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans hc
  have hsum : (X∩S).card+(X∩T).card≤3 := by
    rw [← Finset.card_union_of_disjoint (hST.mono Finset.inter_subset_right Finset.inter_subset_right),he]
    omega
  have hh := hb.rows (X∩S) (X∩T) Finset.inter_subset_right Finset.inter_subset_right hs ht hsum
  rw [he] at hh
  simpa only [endpointBaseClass,if_neg hn0] using hh

theorem endpoint_base_tuple (Q F : SimpleGraph V) (S T W : Finset V) (hST : Disjoint S T)
    (f : Fin 3→V) (hf : ClassSparseGreedyGood Q F (endpointBaseClass S T) W allPreviousLabels f) :
    ∃ C : EndpointTriangle Q F S T,endpointTriangleVertices C=Finset.univ.image f := by
  apply endpoint_triangle_from_tuple Q F S T hST f hf.1
    (by simpa only [endpointBaseClass,Fin.val_zero,ite_true] using (hf.2.1 0).1)
    (fun j=>by simpa [endpointBaseClass] using (hf.2.1 j.succ).1)
    (allPreviousGood_adj Q F _ W f hf) hf.2.2.1

theorem endpoint_base_count (Q F : SimpleGraph V) (S T W : Finset V)
    (hST : Disjoint S T) (L b a : ℝ) (hL : 0≤L) (ha : 0≤a)
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hb : EndpointNeighbourCounts Q F S T b)
    (hbudget : a≤b-((W.card:ℝ)+3)*(L+1)) :
    a^3≤Fintype.card {f : Fin 3→V //
      ClassSparseGreedyGood Q F (endpointBaseClass S T) W allPreviousLabels f} :=
  class_sparse_greedy_sequence_count Q F _ W allPreviousLabels 3 L b a hL ha hF hbudget
    (endpoint_base_common Q F S T W hST b hb)

end Oberwolfach
