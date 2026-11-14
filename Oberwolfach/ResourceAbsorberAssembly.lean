module

public import Oberwolfach.ResourceTransformerChains

@[expose] public section

/-! Attachment followed by a transformer chain. This is the exact
finite decomposition assembly in both ordinary absorber constructions. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W : Type*} [DecidableEq E] [DecidableEq W]

theorem resource_absorber_chain_with_attachment
    (R : W → Finset E) (L T : ℕ → Finset E) (n : ℕ) (hn : 0 < n)
    (original extra : Finset E) (hfirst : L 0=original∪extra)
    (hattach : Disjoint original extra) (hextra : HasResourceDecomposition R extra)
    (htrans : ∀ i, i < n → IsResourceTransformer R (L i) (L (i+1)) (T i))
    (hLL : ∀ i, i ≤ n → ∀ j, j ≤ n → i≠j → Disjoint (L i) (L j))
    (hTT : ∀ i, i < n → ∀ j, j < n → i≠j → Disjoint (T i) (T j))
    (hLT : ∀ i, i ≤ n → ∀ j, j < n → Disjoint (L i) (T j))
    (hfinal : HasResourceDecomposition R (L n)) :
    IsResourceAbsorber R original (extra∪transformerChainEdges L T n∪L n) := by
  have hh := resource_absorber_from_transformer_chain R L T n hn htrans hLL hTT hLT hfinal
  rw [hfirst] at hh
  have ha := resource_absorber_remove_decomposable_part R original extra
    (transformerChainEdges L T n∪L n) hh hattach hextra
  convert ha using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto

theorem resource_absorber_chain_avoids
    (L T : ℕ → Finset E) (n : ℕ) (extra forbidden : Finset E)
    (hextra : Disjoint extra forbidden)
    (hT : ∀ i, i < n → Disjoint (T i) forbidden)
    (hL : ∀ i, 0 < i → i ≤ n → Disjoint (L i) forbidden)
    (hn : 0 < n) :
    Disjoint (extra∪transformerChainEdges L T n∪L n) forbidden := by
  exact Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hextra,transformerChainEdges_disjoint L T n forbidden hT
      (fun i hi hin => hL i hi (Nat.le_of_lt hin))⟩,hL n hn le_rfl⟩

end Oberwolfach
