module

public import Oberwolfach.ResourceCopyWeights
public import Oberwolfach.UniformResourcePadding

@[expose] public section

/-! Incidence identities for rounded copies, including prescribed vertex sets.
Parallel identifiers and the original fixed weight functions are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem resource_copies_degree {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (m : E → ℕ) (v : V) :
    Fintype.card (HypergraphEdgesAt (fun c : (Σ e,Fin (m e))=>R c.1) v)=
      ∑ e,if v∈R e then m e else 0 := by
  classical
  simp only [HypergraphEdgesAt,Fintype.card_subtype,Finset.card_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : v∈R e <;> simp [he]

theorem resource_copies_codegree {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (m : E → ℕ) (u v : V) :
    (Finset.univ.filter (fun c : (Σ e,Fin (m e))=>u∈R c.1 ∧ v∈R c.1)).card=
      ∑ e,if u∈R e ∧ v∈R e then m e else 0 := by
  classical
  simp only [Finset.card_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : u∈R e ∧ v∈R e <;> simp [he]

theorem rounded_resource_codegree_bound {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (w : E → ℝ) (T : ℕ) (hw : ∀ e,0≤w e) (u v : V) :
    ((Finset.univ.filter (fun c : (Σ e,Fin ⌊(T : ℝ)*w e⌋₊)=>u∈R c.1 ∧ v∈R c.1)).card : ℝ)≤
      (T : ℝ)*∑ e,if u∈R e ∧ v∈R e then w e else 0 := by
  rw [resource_copies_codegree]
  exact (sum_floor_scaled_weight_bounds w hw (fun e=>u∈R e ∧ v∈R e) T).2

theorem bounded_rank_weight_mass {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (hsize : ∀ e,2≤(R e).card) (hdeg : ∀ v,hypergraphWeightedDegree R w v≤2) :
    ∑ e,w e≤Fintype.card V := by
  have hl : 2*(∑ e,w e)≤∑ v,hypergraphWeightedDegree R w v := by
    rw [hypergraphWeightedDegree_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize e) (hw e)
  have hu := Finset.sum_le_sum (fun v (_ : v∈Finset.univ)=>hdeg v)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hu
  linarith

theorem rounded_resource_copy_card {V E : Type*} [Fintype V] [Fintype E]
    (w : E → ℝ) (T : ℕ) (hw : ∀ e,0≤w e) (hW : ∑ e,w e≤Fintype.card V) :
    Fintype.card (Σ e,Fin ⌊(T : ℝ)*w e⌋₊)≤T*Fintype.card V := by
  have hh := Finset.sum_le_sum (fun e (_ : e∈Finset.univ)=>Nat.floor_le
    (mul_nonneg (Nat.cast_nonneg T) (hw e)))
  have hh' : ((∑ e,⌊(T : ℝ)*w e⌋₊ : ℕ) : ℝ)≤(T : ℝ)*Fintype.card V := by
    push_cast
    exact hh.trans (by simpa only [← Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg T))
  simpa only [Fintype.card_sigma,Fintype.card_fin] using (by exact_mod_cast hh' :
    (∑ e,⌊(T : ℝ)*w e⌋₊ : ℕ)≤T*Fintype.card V)

theorem resource_set_test_sum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (w : E → ℝ) (S : Finset V) :
    (∑ e,((R e∩S).card : ℝ)*w e)=∑ v∈S,hypergraphWeightedDegree R w v := by
  unfold hypergraphWeightedDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  congr 3
  ext v
  simp only [Finset.mem_filter,Finset.mem_inter,and_comm]

theorem matching_set_test_sum {V E : Type*} [DecidableEq V]
    (R : E → Finset V) (S : Finset V) (M : Finset E)
    (hM : ∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) :
    (∑ e∈M,((R e∩S).card : ℝ))=((S∩M.biUnion R).card : ℝ) := by
  classical
  have hdis : (M : Set E).PairwiseDisjoint (fun e=>R e∩S) := by
    intro e he f hf hef
    exact (hM e he f hf hef).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have heq : M.biUnion (fun e=>R e∩S)=S∩M.biUnion R := by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_inter]
    aesop
  rw [← heq,Finset.card_biUnion hdis]
  simp only [Nat.cast_sum]

end Oberwolfach
