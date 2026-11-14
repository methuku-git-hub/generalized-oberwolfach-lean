module

public import Oberwolfach.OrdinaryExpansionCentralGraph

@[expose] public section

/-! Reindex the private wheels by bijections of the original rim and
spoke identifiers. Equal edge counts therefore give a common central graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E E' J J' W : Type*}

def expansionReindexRow (e : E ≃ E') (j : J ≃ J') :
    ExpansionRow V E J W ≃ ExpansionRow V E' J' W :=
  Equiv.sumCongr (Equiv.refl V) (Equiv.prodCongr (Equiv.sumCongr e j) (Equiv.refl W))

def expansionReindexHub (e : E ≃ E') (j : J ≃ J') :
    ExpansionHub U E J ≃ ExpansionHub U E' J' :=
  Equiv.sumCongr (Equiv.refl U) (Equiv.sumCongr e j)

theorem ordinaryExpansion_reindex_rim (C : SimpleGraph W) (z o : W) (x y : E → V)
    (e : E ≃ E') (j : J ≃ J') (a b : ExpansionRow V E J W) :
    (ordinaryExpansionRim C z o (x ∘ e.symm) (y ∘ e.symm)).Adj
      (expansionReindexRow e j a) (expansionReindexRow e j b) ↔
    (ordinaryExpansionRim C z o x y).Adj a b := by
  rcases a with a|⟨i,w⟩ <;> rcases b with b|⟨i',w'⟩
  · rfl
  · cases i' <;> simp [ordinaryExpansionRim,expansionReindexRow,expansionCrossAdj]
  · cases i <;> simp [ordinaryExpansionRim,expansionReindexRow,expansionCrossAdj]
  · cases i <;> cases i' <;> simp [ordinaryExpansionRim,expansionReindexRow,expansionPrivateAdj]

theorem ordinaryExpansion_reindex_spoke (z : W) (v : J → V) (u : J → U)
    (e : E ≃ E') (j : J ≃ J') (a : ExpansionRow V E J W) (b : ExpansionHub U E J) :
    ordinaryExpansionSpokes z (v ∘ j.symm) (u ∘ j.symm)
      (expansionReindexRow e j a) (expansionReindexHub e j b) ↔ ordinaryExpansionSpokes z v u a b := by
  rcases a with a|⟨i,w⟩ <;> rcases b with b|i'
  · rfl
  · cases i' <;> simp [ordinaryExpansionSpokes,expansionReindexRow,expansionReindexHub]
  · cases i <;> simp [ordinaryExpansionSpokes,expansionReindexRow,expansionReindexHub]
  · cases i <;> cases i' <;> simp [ordinaryExpansionSpokes,expansionReindexRow,expansionReindexHub]

theorem ordinaryExpansion_reindex_graph (C : SimpleGraph W) (z o : W) (x y : E → V)
    (e : E ≃ E') (j : J ≃ J') :
    (ordinaryExpansionRim C z o x y).map (expansionReindexRow (W:=W) e j).toEmbedding=
      ordinaryExpansionRim C z o (x ∘ e.symm) (y ∘ e.symm) := by
  ext a b
  obtain ⟨a,rfl⟩ := (expansionReindexRow (V:=V) (W:=W) e j).surjective a
  obtain ⟨b,rfl⟩ := (expansionReindexRow (V:=V) (W:=W) e j).surjective b
  have hh := SimpleGraph.map_adj_apply (G:=ordinaryExpansionRim C z o x y)
    (f:=(expansionReindexRow (W:=W) e j).toEmbedding) (a:=a) (b:=b)
  exact hh.trans (ordinaryExpansion_reindex_rim C z o x y e j a b).symm

end Oberwolfach
