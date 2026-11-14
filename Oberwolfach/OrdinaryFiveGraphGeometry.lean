module

public import Oberwolfach.OrdinaryEmbeddingGeometry
public import Oberwolfach.OrdinaryRootResources

@[expose] public section

/-! Simultaneous root sets and disjointness of the five actual host pairs.
The same unions control both the transformer exclusions and the final order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryFiveUnion {α:Type} [DecidableEq α] (L R:Finset α) (X:Fin 3→Finset α) : Finset α :=
  L∪R∪Finset.univ.biUnion X

theorem ordinaryFiveUnion_card {α:Type} [DecidableEq α] (L R:Finset α) (X:Fin 3→Finset α)
    (M:ℕ) (hL:L.card≤M) (hR:R.card≤M) (hX:∀ i,(X i).card≤M) :
    (ordinaryFiveUnion L R X).card≤5*M := by
  have hU:(Finset.univ.biUnion X).card≤3*M:=by
    calc
      _≤∑ i:Fin 3,(X i).card:=Finset.card_biUnion_le
      _≤∑ _:Fin 3,M:=Finset.sum_le_sum (fun i _=>hX i)
      _=3*M:=by simp
  exact (Finset.card_union_le _ _).trans (by
    have hLR:=Finset.card_union_le L R
    omega)

theorem ordinaryFiveUnion_left {α:Type} [DecidableEq α] (L R:Finset α) (X:Fin 3→Finset α) :
    L⊆ordinaryFiveUnion L R X:=by intro a ha;exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
theorem ordinaryFiveUnion_right {α:Type} [DecidableEq α] (L R:Finset α) (X:Fin 3→Finset α) :
    R⊆ordinaryFiveUnion L R X:=by intro a ha;exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
theorem ordinaryFiveUnion_mid {α:Type} [DecidableEq α] (L R:Finset α) (X:Fin 3→Finset α) (i:Fin 3) :
    X i⊆ordinaryFiveUnion L R X:=by
  intro a ha;exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩)

variable {VL UL VR UR V U:Type} [Fintype VL] [Fintype UL] [Fintype VR] [Fintype UR]
    [Fintype V] [Fintype U] [DecidableEq VL] [DecidableEq UL] [DecidableEq VR] [DecidableEq UR]
    [DecidableEq V] [DecidableEq U]
    {Vm Um:Fin 3→Type} [∀ i,Fintype (Vm i)] [∀ i,Fintype (Um i)]
    [∀ i,DecidableEq (Vm i)] [∀ i,DecidableEq (Um i)]

theorem ordinary_five_graph_geometry
    (Gleft:SimpleGraph VL) (HL:VL→UL→Prop) (Gright:SimpleGraph VR) (HR:VR→UR→Prop)
    (Gm:∀ i,SimpleGraph (Vm i)) (Hm:∀ i,Vm i→Um i→Prop)
    (Q F:SimpleGraph V) (H:V→U→Prop)
    (eL:OrdinaryPairHostEmbedding Gleft HL Q H) (eR:OrdinaryPairHostEmbedding Gright HR Q H)
    (e:∀ i,OrdinaryPairHostEmbedding (Gm i) (Hm i) Q H)
    (A W R₀:Finset V) (B₀:Finset U)
    (hR:eR.IsFresh F A W (R₀∪Finset.univ.image eL.row) (B₀∪Finset.univ.image eL.hub))
    (hm:∀ i,(e i).IsFresh F A W ((R₀∪Finset.univ.image eL.row)∪Finset.univ.image eR.row)
      ((B₀∪Finset.univ.image eL.hub)∪Finset.univ.image eR.hub))
    (hd:∀ i j,i≠j→∀ a b,(e i).row a≠(e j).row b) :
    let D:Fin 5→Finset (Sym2 V⊕(V×U)):=![eL.resources,(e 0).resources,(e 1).resources,(e 2).resources,eR.resources]
    let R:=ordinaryFiveUnion (Finset.univ.image eL.row) (Finset.univ.image eR.row) (fun i=>Finset.univ.image (e i).row)
    let B:=ordinaryFiveUnion (Finset.univ.image eL.hub) (Finset.univ.image eR.hub) (fun i=>Finset.univ.image (e i).hub)
    (∀ i j,i≠j→Disjoint (D i) (D j))∧
    (∀ i,ordinaryResourceRows (D i)⊆R)∧
    (∀ i,ordinaryResourceHubs (D i)⊆B)∧
    (∀ i,D i⊆ordinaryHostResources Q H) := by
  dsimp only
  have hLR:Disjoint eL.resources eR.resources:=by
    apply eL.resources_disjoint eR
    intro a b heq
    exact (hR.1 b).2.2.1 (by rw [←heq];simp)
  have hLm (i:Fin 3):Disjoint eL.resources (e i).resources:=by
    apply eL.resources_disjoint (e i)
    intro a b heq
    exact ((hm i).1 b).2.2.1 (by rw [←heq];simp)
  have hRm (i:Fin 3):Disjoint eR.resources (e i).resources:=by
    apply eR.resources_disjoint (e i)
    intro a b heq
    exact ((hm i).1 b).2.2.1 (by rw [←heq];simp)
  have hmm (i j:Fin 3) (hij:i≠j):Disjoint (e i).resources (e j).resources:=
    (e i).resources_disjoint (e j) (hd i j hij)
  refine ⟨?_,?_,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    · exact (hij rfl).elim
    · exact hLm 0
    · exact hLm 1
    · exact hLm 2
    · exact hLR
    · exact (hLm 0).symm
    · exact (hij rfl).elim
    · exact hmm 0 1 (by decide)
    · exact hmm 0 2 (by decide)
    · exact (hRm 0).symm
    · exact (hLm 1).symm
    · exact hmm 1 0 (by decide)
    · exact (hij rfl).elim
    · exact hmm 1 2 (by decide)
    · exact (hRm 1).symm
    · exact (hLm 2).symm
    · exact hmm 2 0 (by decide)
    · exact hmm 2 1 (by decide)
    · exact (hij rfl).elim
    · exact (hRm 2).symm
    · exact hLR.symm
    · exact hRm 0
    · exact hRm 1
    · exact hRm 2
    · exact (hij rfl).elim
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    · exact eL.resource_rows.trans (ordinaryFiveUnion_left _ _ _)
    · exact (e 0).resource_rows.trans (ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).row) 0)
    · exact (e 1).resource_rows.trans (ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).row) 1)
    · exact (e 2).resource_rows.trans (ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).row) 2)
    · exact eR.resource_rows.trans (ordinaryFiveUnion_right _ _ _)
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    · exact eL.resource_hubs.trans (ordinaryFiveUnion_left _ _ _)
    · exact (e 0).resource_hubs.trans (ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).hub) 0)
    · exact (e 1).resource_hubs.trans (ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).hub) 1)
    · exact (e 2).resource_hubs.trans (ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).hub) 2)
    · exact eR.resource_hubs.trans (ordinaryFiveUnion_right _ _ _)
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    · exact eL.resources_subset
    · exact (e 0).resources_subset
    · exact (e 1).resources_subset
    · exact (e 2).resources_subset
    · exact eR.resources_subset

theorem OrdinaryPairHostEmbedding.resources_avoid_roots
    {Gleft:SimpleGraph VL} {HL:VL→UL→Prop} {Q:SimpleGraph V} {H:V→U→Prop}
    (e:OrdinaryPairHostEmbedding Gleft HL Q H) (S:Finset V) (B:Finset U)
    (h:∀ a,e.row a∉S) : Disjoint e.resources (ordinaryRootResources S B) := by
  apply ordinary_resources_disjoint_of_rows
  apply (show Disjoint (Finset.univ.image e.row) S from ?_).mono e.resource_rows (ordinaryRootResources_rows S B)
  apply Finset.disjoint_left.mpr
  rintro v hv hv'
  obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
  exact h a hv'

end Oberwolfach
