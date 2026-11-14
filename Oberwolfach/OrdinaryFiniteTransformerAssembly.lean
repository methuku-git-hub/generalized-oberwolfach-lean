module

public import Oberwolfach.ResourceAbsorberAssembly
public import Oberwolfach.OrdinarySequentialResourceSelection

@[expose] public section

/-! The ordinary four-transformer diagram, with its alternating map
orientations. The input transformers have already been constructed in a common
host. This assembly includes every intermediate graph exactly once. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E C:Type} [DecidableEq E] [DecidableEq C]

def finiteTransformerAt (K:Fin 4→Finset E) (i:ℕ) : Finset E :=
  if h:i<4 then K ⟨i,h⟩ else ∅

theorem finiteTransformerAt_apply (K:Fin 4→Finset E) (i:Fin 4) :
    finiteTransformerAt K i.val=K i := by simp [finiteTransformerAt,i.isLt]

theorem finite_four_transformer_absorber (R:C→Finset E)
    (L:ℕ→Finset E) (S T:Fin 4→Finset E) (K:Fin 4→Finset E)
    (original extra forbidden:Finset E)
    (hfirst:L 0=original∪extra) (hattach:Disjoint original extra)
    (hextra:HasResourceDecomposition R extra)
    (hfinal:HasResourceDecomposition R (L 4))
    (htrans:∀ i,IsResourceTransformer R (S i) (T i) (K i))
    (hends:∀ i:Fin 4,(S i=L i.val∧T i=L (i.val+1))∨(S i=L (i.val+1)∧T i=L i.val))
    (hLL:∀ i,i≤4→∀ j,j≤4→i≠j→Disjoint (L i) (L j))
    (hKK:∀ i j,i≠j→Disjoint (K i) (K j))
    (hKL:∀ i,Disjoint (K i) forbidden)
    (hL:∀ i,i≤4→L i⊆forbidden) :
    IsResourceAbsorber R original
      (extra∪transformerChainEdges L (finiteTransformerAt K) 4∪L 4) := by
  apply resource_absorber_chain_with_attachment R L (finiteTransformerAt K) 4 (by omega)
    original extra hfirst hattach hextra
  · intro i hi
    let j:Fin 4:=⟨i,hi⟩
    have hk:finiteTransformerAt K i=K j:=finiteTransformerAt_apply K j
    rw [hk]
    rcases hends j with ⟨hs,ht⟩|⟨hs,ht⟩
    · simpa only [hs,ht] using htrans j
    · simpa only [hs,ht] using resource_transformer_symm R (S j) (T j) (K j) (htrans j)
  · exact hLL
  · intro i hi j hj hij
    rw [show finiteTransformerAt K i=K ⟨i,hi⟩ from finiteTransformerAt_apply K ⟨i,hi⟩,
      show finiteTransformerAt K j=K ⟨j,hj⟩ from finiteTransformerAt_apply K ⟨j,hj⟩]
    exact hKK _ _ (fun h=>hij (congrArg Fin.val h))
  · intro i hi j hj
    rw [show finiteTransformerAt K j=K ⟨j,hj⟩ from finiteTransformerAt_apply K ⟨j,hj⟩]
    exact ((hKL ⟨j,hj⟩).mono_right (hL i hi)).symm
  · exact hfinal

end Oberwolfach
