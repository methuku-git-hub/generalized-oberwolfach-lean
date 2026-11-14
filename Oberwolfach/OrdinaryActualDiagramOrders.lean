module

public import Oberwolfach.OrdinaryActualDiagramModels

@[expose] public section

/-! Uniform finite order bounds for both attachments and the three
expansions, before choosing any labels in the ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀:Type} [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]

theorem ordinary_actual_diagram_orders (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop)
    (r m:ℕ) (hr:3≤r) (hm:Fintype.card V₀+Fintype.card U₀≤m) :
    let k:=G.edgeFinset.card/r
    let Gc:=ordinaryComparisonRim r k (by omega)
    let Hc:=ordinaryComparisonSpokes r k (by omega)
    (Fintype.card (ActualExpansionRow G Hs (Fin r))+Fintype.card (ActualExpansionHub G Hs)≤ordinaryDiagramSize r m)∧
    (Fintype.card (ActualExpansionRow Gc Hc (Fin r))+Fintype.card (ActualExpansionHub Gc Hc)≤ordinaryDiagramSize r m)∧
    (∀ i:Fin 3,Fintype.card (ExpansionRow (ordinaryDiagramOldRows G r i) (ordinaryDiagramEdges G r hr i)
        (ordinaryDiagramSpokes G Hs r hr i) (Fin r))+
      Fintype.card (ExpansionHub (ordinaryDiagramOldHubs (U₀:=U₀) G r i) (ordinaryDiagramEdges G r hr i)
        (ordinaryDiagramSpokes G Hs r hr i))≤ordinaryDiagramSize r m) := by
  dsimp only
  refine ⟨(actual_expansion_order_bound G Hs r m hm).trans ?_,?_,?_⟩
  · dsimp [ordinaryDiagramSize];omega
  · have hJ:=ordinary_comparison_order_bound G r m (by omega)
    exact (actual_expansion_order_bound _ _ r (m^2*(r+2)) hJ).trans (by dsimp [ordinaryDiagramSize];omega)
  · intro i
    rw [ordinaryExpansion_order]
    simpa only [Fintype.card_fin] using ordinary_diagram_model_size G Hs r m hr hm i

end Oberwolfach
