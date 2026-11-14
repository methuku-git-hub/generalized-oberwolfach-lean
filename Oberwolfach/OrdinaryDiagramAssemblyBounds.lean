module

public import Oberwolfach.OrdinaryDiagramEndpoints

@[expose] public section

/-! Endpoint, size and forbidden-resource conclusions of the actual
four-transformer absorber. Bounds count the same finite unions that occur
in the exact decomposition identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {r M:ℕ} {Q F:SimpleGraph V} {H:V→U→Prop}
    {original:Finset (Sym2 V⊕(V×U))} {A W R₀:Finset V} {B₀ O:Finset U}

def ordinaryDiagramAbsorberEdges
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O)
    (K:Fin 4→Finset (Sym2 V⊕(V×U))) :=
  D.extra∪transformerChainEdges (finiteFiveAt D.D) (finiteTransformerAt K) 4∪D.D 4

theorem ordinaryDiagramAbsorberEdges_subset
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O)
    (K:Fin 4→Finset (Sym2 V⊕(V×U))) :
    ordinaryDiagramAbsorberEdges D K⊆Finset.univ.biUnion D.D∪Finset.univ.biUnion K := by
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · rcases Finset.mem_union.mp he with he|he
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨0,Finset.mem_univ _,?_⟩
      rw [D.first];exact Finset.mem_union_right _ he
    · rcases (mem_transformerChainEdges _ _ _ _).mp he with ⟨i,hi,he⟩|⟨i,_,hi,he⟩
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,by simpa only [finiteTransformerAt_apply K ⟨i,hi⟩] using he⟩
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨⟨i,by omega⟩,Finset.mem_univ _,by simpa only [finiteFiveAt_apply D.D ⟨i,by omega⟩] using he⟩
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨4,Finset.mem_univ _,he⟩)

theorem ordinary_diagram_assembly_bounds
    (D:OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O)
    (K:Fin 4→Finset (Sym2 V⊕(V×U))) (a b:ℕ)
    (hKhost:∀ j,K j⊆ordinaryHostResources Q H)
    (hKrows:∀ j,ordinaryResourceRows (K j)⊆D.rows∪A)
    (hKavoid:∀ j,∀ v∈ordinaryResourceRows (K j),v∈W∪D.rows→v∈D.rows)
    (hKhubs:∀ j,∀ u∈ordinaryResourceHubs (K j),u∈B₀∪D.hubs→
      ∃ i:{u:U // ∃ v,(D.T j).K v u},u=i.val∨u=(D.T j).ψ i.val)
    (hKdis:∀ j,Disjoint (K j) (ordinaryRootResources D.rows (B₀∪D.hubs)))
    (hKcard:(ordinaryResourceRows (Finset.univ.biUnion K)).card≤a)
    (hHcard:(ordinaryResourceHubs (Finset.univ.biUnion K)).card≤b) :
    let C:=ordinaryDiagramAbsorberEdges D K
    C⊆ordinaryHostResources Q H∧
    (ordinaryResourceRows C).card≤5*M+a∧(ordinaryResourceHubs C).card≤5*M+b∧
    ordinaryResourceRows C⊆R₀∪A∧
    (∀ v∈ordinaryResourceRows C,v∈W→v∈R₀)∧
    (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈O)∧
    Disjoint C (ordinaryRootResources W B₀) := by
  dsimp only
  have hDrows:ordinaryResourceRows (Finset.univ.biUnion D.D)⊆D.rows:=by
    rw [ordinaryResourceRows_biUnion]
    exact Finset.biUnion_subset.mpr (fun i _=>D.Drows i)
  have hDhubs:ordinaryResourceHubs (Finset.univ.biUnion D.D)⊆D.hubs:=by
    rw [ordinaryResourceHubs_biUnion]
    exact Finset.biUnion_subset.mpr (fun i _=>D.Dhubs i)
  have hrows:ordinaryResourceRows (ordinaryDiagramAbsorberEdges D K)⊆D.rows∪ordinaryResourceRows (Finset.univ.biUnion K):=by
    have hh:=ordinaryResourceRows_mono (ordinaryDiagramAbsorberEdges_subset D K)
    rw [ordinaryResourceRows_union] at hh
    exact hh.trans (Finset.union_subset_union hDrows (fun _ h=>h))
  have hhubs:ordinaryResourceHubs (ordinaryDiagramAbsorberEdges D K)⊆D.hubs∪ordinaryResourceHubs (Finset.univ.biUnion K):=by
    have hh:=ordinaryResourceHubs_mono (ordinaryDiagramAbsorberEdges_subset D K)
    rw [ordinaryResourceHubs_union] at hh
    exact hh.trans (Finset.union_subset_union hDhubs (fun _ h=>h))
  have hub_allowed (j:Fin 4) (u:U) (hu:u∈ordinaryResourceHubs (K j)) (huB:u∈B₀):u∈O:=by
    obtain ⟨i,hi⟩:=hKhubs j u hu (Finset.mem_union_left _ huB)
    have huD:u∈D.hubs:=by rcases hi with rfl|rfl;exact (D.active_hubs j i).1;exact (D.active_hubs j i).2
    exact D.hubs_avoid u huD huB
  have hroot:ordinaryRootResources W B₀⊆ordinaryRootResources (R₀∪W) B₀:=
    ordinaryRootResources_contains _ _ _ ((ordinaryRootResources_rows W B₀).trans Finset.subset_union_right)
      (ordinaryRootResources_hubs W B₀)
  have hKavoidRoot (j:Fin 4):Disjoint (K j) (ordinaryRootResources W B₀):=by
    obtain ⟨hrr,hrb⟩:=ordinaryRootResources_avoid (K j) D.rows (B₀∪D.hubs) (hKdis j)
    apply ordinary_transformer_forbidden_edges (K j) (ordinaryRootResources W B₀) D.rows (W∪D.rows) (B₀∪D.hubs)
      ((ordinaryRootResources_rows W B₀).trans Finset.subset_union_left)
      ((ordinaryRootResources_hubs W B₀).trans Finset.subset_union_left)
    · intro v hv w he
      exact hKavoid j v (Finset.mem_biUnion.mpr ⟨_,he,by simp⟩) hv
    · intro v hv u he
      exact hKavoid j v (Finset.mem_biUnion.mpr ⟨_,he,by simp⟩) hv
    · exact hrr
    · exact hrb
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · apply (ordinaryDiagramAbsorberEdges_subset D K).trans
    exact Finset.union_subset (Finset.biUnion_subset.mpr (fun i _=>D.host i))
      (Finset.biUnion_subset.mpr (fun i _=>hKhost i))
  · exact (Finset.card_le_card hrows).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add D.rows_card hKcard))
  · exact (Finset.card_le_card hhubs).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add D.hubs_card hHcard))
  · intro v hv
    rcases Finset.mem_union.mp (hrows hv) with hv|hv
    · exact D.rows_location hv
    · rw [ordinaryResourceRows_biUnion] at hv
      obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      rcases Finset.mem_union.mp (hKrows i hv) with hv|hv
      · exact D.rows_location hv
      · exact Finset.mem_union_right _ hv
  · intro v hv hvW
    rcases Finset.mem_union.mp (hrows hv) with hv|hv
    · exact D.rows_avoid v hv hvW
    · rw [ordinaryResourceRows_biUnion] at hv
      obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      exact D.rows_avoid v (hKavoid i v hv (Finset.mem_union_left _ hvW)) hvW
  · intro u hu huB
    rcases Finset.mem_union.mp (hhubs hu) with hu|hu
    · exact D.hubs_avoid u hu huB
    · rw [ordinaryResourceHubs_biUnion] at hu
      obtain ⟨i,_,hu⟩:=Finset.mem_biUnion.mp hu
      exact hub_allowed i u hu huB
  · change Disjoint (D.extra∪transformerChainEdges (finiteFiveAt D.D) (finiteTransformerAt K) 4∪D.D 4) _
    have hlast:finiteFiveAt D.D 4=D.D 4:=finiteFiveAt_apply D.D (4:Fin 5)
    rw [←hlast]
    apply resource_absorber_chain_avoids _ _ _ _ _ (D.extra_avoid.mono_right hroot) _ _ (by omega)
    · intro i hi
      rw [show finiteTransformerAt K i=K ⟨i,hi⟩ from finiteTransformerAt_apply K ⟨i,hi⟩]
      exact hKavoidRoot ⟨i,hi⟩
    · intro i hi hi4
      rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩]
      exact (D.avoid _ (by intro h;have hh:=congrArg Fin.val h;dsimp at hh;omega)).mono_right hroot

end Oberwolfach
