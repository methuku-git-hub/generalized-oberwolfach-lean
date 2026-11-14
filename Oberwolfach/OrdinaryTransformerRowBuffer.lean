module

public import Oberwolfach.TransformerActiveHubSpokes

@[expose] public section

/-! The old and image root edges are disjoint because their row supports
are disjoint, not because either map is injective on vertices. The row
buffer for later hub trades includes the actual vertex wheels and has
an explicit bound independent of their choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem transformer_root_resources_disjoint (G:SimpleGraph V) (H₀:V→U→Prop) (φ:V→V) (ψ:U→U)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w):
    Disjoint (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  rcases Finset.mem_union.mp hf with hf|hf
  · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
    rw [←hi,ordinaryHostResources_rim,SimpleGraph.mem_edgeSet] at he
    exact hcross _ (edge_out_adj G i).mem_support_left _ he.mem_support_left rfl
  · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
    rw [←hi,ordinaryHostResources_spoke] at he
    exact hcross _ (balanced_spoke_root_mem_support G H₀ hbalance i) _
      (balanced_spoke_root_mem_support G H₀ hbalance ⟨(φ i.val.1,ψ i.val.2),he⟩) rfl

 theorem ordinary_transformer_row_buffer
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U) (r:ℕ)
    (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d)):
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    ∃ W':Finset V,W⊆W'∧W'.card≤W.card+2*r*Fintype.card (Σ v,G.neighborSet v)∧
      (∀ i,∀ v∈(ordinaryWheelRim (Plus i)).support,v∈W')∧
      (∀ i,∀ v∈(ordinaryWheelRim (Minus i)).support,v∈W'):=by
  dsimp only
  let C:Finset V:=(wheelFamilyRim (fun d=>(D d).first)).support.toFinset
  let C':Finset V:=(wheelFamilyRim (fun d=>(D d).second)).support.toFinset
  have hC:C.card≤r*Fintype.card (Σ v,G.neighborSet v):=(wheelFamily_vertex_bound (fun d=>(D d).first)).1
  have hC':C'.card≤r*Fintype.card (Σ v,G.neighborSet v):=(wheelFamily_vertex_bound (fun d=>(D d).second)).1
  have hfirst (d:Σ v,G.neighborSet v) (v:V) (hv:v∈(ordinaryWheelRim (D d).first).support):v∈C:=by
    apply Set.mem_toFinset.mpr
    obtain ⟨w,hw⟩:=hv
    exact ⟨w,SimpleGraph.iSup_adj.mpr ⟨d,hw⟩⟩
  have hsecond (d:Σ v,G.neighborSet v) (v:V) (hv:v∈(ordinaryWheelRim (D d).second).support):v∈C':=by
    apply Set.mem_toFinset.mpr
    obtain ⟨w,hw⟩:=hv
    exact ⟨w,SimpleGraph.iSup_adj.mpr ⟨d,hw⟩⟩
  let W':=W∪C∪C'
  have hWW:W⊆W':=Finset.subset_union_left.trans Finset.subset_union_left
  have hCW:C⊆W':=Finset.subset_union_right.trans Finset.subset_union_left
  have hC'W:C'⊆W':=Finset.subset_union_right
  refine ⟨W',hWW,?_,?_,?_⟩
  · have hsum:=Finset.card_union_le (W∪C) C'
    have hsum':=Finset.card_union_le W C
    dsimp only [W']
    nlinarith only [hsum,hsum',hC,hC']
  · intro i v hv
    rcases i with i|(i|i)
    · rcases (E.first_support i v).mp hv with he|he|he
      · exact hWW (hRW (he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_left).1))
      · exact hWW (hRW (he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_right).1))
      · exact hWW (hpW _ _ he)
    · rcases (S.first_support i v).mp hv with he|he
      · exact hWW (hRW (he.symm ▸ (hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)).1))
      · exact hWW (hpW _ _ he)
    · exact hC'W (hsecond i v hv)
  · intro i v hv
    rcases i with i|(i|i)
    · rcases (E.second_support i v).mp hv with he|he|he
      · exact hWW (hRW (he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_left).2))
      · exact hWW (hRW (he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_right).2))
      · exact hWW (hpW _ _ he)
    · rcases (S.second_support i v).mp hv with he|he
      · exact hWW (hRW (he.symm ▸ (hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)).2))
      · exact hWW (hpW _ _ he)
    · exact hCW (hfirst i v hv)

end Oberwolfach
