module

public import Oberwolfach.OrdinaryHostDiagram
public import Oberwolfach.OrdinaryFiniteTransformerAssembly

@[expose] public section

/-! Exact endpoint identities for the alternating four-transformer
chain, and the root-hub locations needed by its actual ambient caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def finiteFiveAt {E:Type} (D:Fin 5→Finset E) (i:ℕ) : Finset E :=
  if h:i<5 then D ⟨i,h⟩ else ∅

theorem finiteFiveAt_apply {E:Type} (D:Fin 5→Finset E) (i:Fin 5) :
    finiteFiveAt D i.val=D i := by simp [finiteFiveAt,i.isLt]

variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {r M:ℕ} {Q F:SimpleGraph V} {H:V→U→Prop}
    {original:Finset (Sym2 V⊕(V×U))} {A W R₀:Finset V} {B₀ O:Finset U}

theorem OrdinaryHostDiagram.chain_endpoints
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O) :
    ∀ j:Fin 4,
      (ordinaryHostResources (D.T j).G (D.T j).K=finiteFiveAt D.D j.val∧
        transformerImageResources (D.T j).G (D.T j).K (D.T j).φ (D.T j).ψ=finiteFiveAt D.D (j.val+1))∨
      (ordinaryHostResources (D.T j).G (D.T j).K=finiteFiveAt D.D (j.val+1)∧
        transformerImageResources (D.T j).G (D.T j).K (D.T j).φ (D.T j).ψ=finiteFiveAt D.D j.val) := by
  intro j
  rw [D.source,D.target]
  fin_cases j <;> simp [finiteFiveAt]

theorem OrdinaryHostDiagram.chain_disjoint
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O) :
    ∀ i,i≤4→∀ j,j≤4→i≠j→Disjoint (finiteFiveAt D.D i) (finiteFiveAt D.D j) := by
  intro i hi j hj hij
  rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩,
    show finiteFiveAt D.D j=D.D ⟨j,by omega⟩ from finiteFiveAt_apply D.D ⟨j,by omega⟩]
  exact D.disjoint _ _ (fun h=>hij (congrArg Fin.val h))

theorem OrdinaryHostDiagram.source_hubs
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O) (j:Fin 4) :
    ordinaryResourceHubs (ordinaryHostResources (D.T j).G (D.T j).K)⊆D.hubs := by
  rw [D.source]
  fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact D.Dhubs 1
  · exact D.Dhubs 1
  · exact D.Dhubs 3
  · exact D.Dhubs 3

theorem OrdinaryHostDiagram.target_hubs
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O) (j:Fin 4) :
    ordinaryResourceHubs (transformerImageResources (D.T j).G (D.T j).K (D.T j).φ (D.T j).ψ)⊆D.hubs := by
  rw [D.target]
  fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact D.Dhubs 0
  · exact D.Dhubs 2
  · exact D.Dhubs 2
  · exact D.Dhubs 4

theorem OrdinaryHostDiagram.active_hubs
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O) (j:Fin 4)
    (i:{u:U // ∃ v,(D.T j).K v u}) : i.val∈D.hubs∧(D.T j).ψ i.val∈D.hubs := by
  obtain ⟨v,hv⟩:=i.property
  have hs:Sum.inr (v,i.val)∈ordinaryHostResources (D.T j).G (D.T j).K:=
    (ordinaryHostResources_spoke _ _ _ _).mpr hv
  have ht:Sum.inr ((D.T j).φ v,(D.T j).ψ i.val)∈
      transformerImageResources (D.T j).G (D.T j).K (D.T j).φ (D.T j).ψ:=by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨(v,i.val),hv⟩,Finset.mem_univ _,rfl⟩)
  exact ⟨D.source_hubs j (Finset.mem_biUnion.mpr ⟨_,hs,by simp⟩),
    D.target_hubs j (Finset.mem_biUnion.mpr ⟨_,ht,by simp⟩)⟩

end Oberwolfach
