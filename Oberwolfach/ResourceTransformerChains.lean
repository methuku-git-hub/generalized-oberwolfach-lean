module

public import Oberwolfach.ResourceTransformers
public import Mathlib.Data.Finset.Range

@[expose] public section

/-! Composition of a finite chain of edge-disjoint transformers. Every
intermediate remainder is included exactly once. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W : Type*} [DecidableEq E] [DecidableEq W]

def transformerChainEdges (L T : ℕ → Finset E) (n : ℕ) : Finset E :=
  (Finset.range n).biUnion T ∪ ((Finset.range n).erase 0).biUnion L

theorem transformerChainEdges_one (L T : ℕ → Finset E) :
    transformerChainEdges L T 1=T 0 := by simp [transformerChainEdges]

theorem mem_transformerChainEdges (L T : ℕ → Finset E) (n : ℕ) (e : E) :
    e∈transformerChainEdges L T n ↔
      (∃ i, i < n ∧ e∈T i) ∨ (∃ i, 0 < i ∧ i < n ∧ e∈L i) := by
  simp only [transformerChainEdges,Finset.mem_union,Finset.mem_biUnion,
    Finset.mem_range,Finset.mem_erase]
  constructor
  · rintro (⟨i,hi,he⟩|⟨i,⟨hi0,hin⟩,he⟩)
    · exact Or.inl ⟨i,hi,he⟩
    · exact Or.inr ⟨i,by omega,hin,he⟩
  · rintro (⟨i,hi,he⟩|⟨i,hi0,hin,he⟩)
    · exact Or.inl ⟨i,hi,he⟩
    · exact Or.inr ⟨i,⟨by omega,hin⟩,he⟩

theorem transformerChainEdges_step (L T : ℕ → Finset E) (n : ℕ) (hn : 0 < n) :
    transformerChainEdges L T (n+1)=transformerChainEdges L T n ∪ L n ∪ T n := by
  ext e
  simp only [mem_transformerChainEdges,Finset.mem_union]
  constructor
  · rintro (⟨i,hi,he⟩|⟨i,hi0,hi,he⟩)
    · by_cases hin : i=n
      · subst i;exact Or.inr he
      · exact Or.inl (Or.inl (Or.inl ⟨i,by omega,he⟩))
    · by_cases hin : i=n
      · subst i;exact Or.inl (Or.inr he)
      · exact Or.inl (Or.inl (Or.inr ⟨i,hi0,by omega,he⟩))
  · rintro ((h|h)|h)
    · rcases h with ⟨i,hi,he⟩|⟨i,hi0,hi,he⟩
      · exact Or.inl ⟨i,by omega,he⟩
      · exact Or.inr ⟨i,hi0,by omega,he⟩
    · exact Or.inr ⟨n,hn,by omega,h⟩
    · exact Or.inl ⟨n,by omega,h⟩

theorem transformerChainEdges_disjoint
    (L T : ℕ → Finset E) (n : ℕ) (S : Finset E)
    (hT : ∀ i, i < n → Disjoint (T i) S)
    (hL : ∀ i, 0 < i → i < n → Disjoint (L i) S) :
    Disjoint (transformerChainEdges L T n) S := by
  apply Finset.disjoint_left.mpr
  intro e he hs
  rcases (mem_transformerChainEdges L T n e).mp he with ⟨i,hi,he⟩|⟨i,hi0,hi,he⟩
  · exact (Finset.disjoint_left.mp (hT i hi)) he hs
  · exact (Finset.disjoint_left.mp (hL i hi0 hi)) he hs

theorem resource_transformer_chain (R : W → Finset E) (L T : ℕ → Finset E)
    (n : ℕ) (hn : 0 < n)
    (htrans : ∀ i, i < n → IsResourceTransformer R (L i) (L (i+1)) (T i))
    (hLL : ∀ i, i ≤ n → ∀ j, j ≤ n → i ≠ j → Disjoint (L i) (L j))
    (hTT : ∀ i, i < n → ∀ j, j < n → i ≠ j → Disjoint (T i) (T j))
    (hLT : ∀ i, i ≤ n → ∀ j, j < n → Disjoint (L i) (T j)) :
    IsResourceTransformer R (L 0) (L n) (transformerChainEdges L T n) := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      simpa [transformerChainEdges] using htrans 0 (by omega)
    · have hkpos : 0 < k := by omega
      have hprev := ih hkpos (fun i hi => htrans i (by omega))
        (fun i hi j hj hij => hLL i (by omega) j (by omega) hij)
        (fun i hi j hj hij => hTT i (by omega) j (by omega) hij)
        (fun i hi j hj => hLT i (by omega) j (by omega))
      rw [transformerChainEdges_step L T k hkpos]
      apply resource_transformer_compose R (L 0) (L k) (L (k+1))
        (transformerChainEdges L T k) (T k) hprev (htrans k (by omega))
        (hLL 0 (by omega) k (by omega) (by omega))
        (hLL k (by omega) (k+1) (by omega) (by omega))
      · exact transformerChainEdges_disjoint L T k (T k)
          (fun i hi => hTT i (by omega) k (by omega) (by omega))
          (fun i _ hi => hLT i (by omega) k (by omega))
      · exact transformerChainEdges_disjoint L T k (L (k+1))
          (fun i hi => (hLT (k+1) (by omega) i (by omega)).symm)
          (fun i _ hi => hLL i (by omega) (k+1) (by omega) (by omega))
      · exact hLT 0 (by omega) k (by omega)

theorem resource_absorber_from_transformer_chain
    (R : W → Finset E) (L T : ℕ → Finset E) (n : ℕ) (hn : 0 < n)
    (htrans : ∀ i, i < n → IsResourceTransformer R (L i) (L (i+1)) (T i))
    (hLL : ∀ i, i ≤ n → ∀ j, j ≤ n → i ≠ j → Disjoint (L i) (L j))
    (hTT : ∀ i, i < n → ∀ j, j < n → i ≠ j → Disjoint (T i) (T j))
    (hLT : ∀ i, i ≤ n → ∀ j, j < n → Disjoint (L i) (T j))
    (hfinal : HasResourceDecomposition R (L n)) :
    IsResourceAbsorber R (L 0) (transformerChainEdges L T n ∪ L n) := by
  exact resource_transformer_to_absorber R (L 0) (L n) (transformerChainEdges L T n)
    (resource_transformer_chain R L T n hn htrans hLL hTT hLT)
    (hLL 0 (by omega) n le_rfl (by omega)) hfinal

end Oberwolfach
