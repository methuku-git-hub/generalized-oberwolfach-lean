module

public import Oberwolfach.RowCoverUnion

@[expose] public section

/-! Remove wheels that miss the designated row root. Root edges remain
covered, all physical resources only decrease, and every retained wheel
meets the list of designated row roots in exactly its own root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinaryWheelRimGraph_mono {M N:Finset (OrdinaryWheel Q F H r)} (hMN:M⊆N):
    ordinaryWheelRimGraph M≤ordinaryWheelRimGraph N:=by
  intro a b hab
  obtain ⟨W,hW,hab⟩:=(ordinaryWheelRimGraph_edges M s(a,b)).mp hab
  exact (ordinaryWheelRimGraph_edges N s(a,b)).mpr ⟨W,hMN hW,hab⟩

theorem ordinaryPackingSpokes_mono {M N:Finset (OrdinaryWheel Q F H r)} (hMN:M⊆N)
    (a:V) (u:U) (h:ordinaryPackingSpokes M a u):ordinaryPackingSpokes N a u:=by
  obtain ⟨W,hW,hh,ha⟩:=h
  exact ⟨W,hMN hW,hh,ha⟩

theorem OrdinaryRowCover.filter_root {M:Finset (OrdinaryWheel Q F H r)} {x:V} {A:Finset V} {K:ℕ}
    (hM:OrdinaryRowCover M x A K):
    OrdinaryRowCover (M.filter (fun W=>x∈(ordinaryWheelRim W).support)) x A K:=by
  let N:=M.filter (fun W=>x∈(ordinaryWheelRim W).support)
  have hNM:N⊆M:=Finset.filter_subset _ _
  have hR:=ordinaryWheelRimGraph_mono hNM
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    exact hM.disjoint W (hNM hW) Z (hNM hZ) hne
  · intro W hW a ha
    exact hM.support W (hNM hW) a ha
  · intro a
    constructor
    · intro h;exact (hM.rims a).mp (hR h)
    · intro h
      obtain ⟨W,hW,ha⟩:=(ordinaryWheelRimGraph_edges M s(x,a)).mp ((hM.rims a).mpr h)
      exact (ordinaryWheelRimGraph_edges N s(x,a)).mpr ⟨W,Finset.mem_filter.mpr ⟨hW,ha.mem_support_left⟩,ha⟩
  · intro u
    constructor
    · intro h;exact (hM.spokes u).mp (ordinaryPackingSpokes_mono hNM x u h)
    · intro h
      obtain ⟨W,hW,hh,hx⟩:=(hM.spokes u).mpr h
      exact ⟨W,Finset.mem_filter.mpr ⟨hW,hx⟩,hh,hx⟩
  · intro a ha
    exact (SimpleGraph.degree_le_of_le hR).trans (hM.rimDegree a ha)
  · intro a ha
    apply le_trans (Finset.card_le_card ?_) (hM.rowDegree a ha)
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ordinaryPackingSpokes_mono hNM a u (Finset.mem_filter.mp hu).2⟩
  · intro u
    apply le_trans (Finset.card_le_card ?_) (hM.columnDegree u)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ordinaryPackingSpokes_mono hNM a u (Finset.mem_filter.mp ha).2⟩

theorem rooted_ordinary_row_cover_family {n K:ℕ}
    (M:Fin n→Finset (OrdinaryWheel Q F H r)) (x:Fin n→V) (A:Finset V)
    (hx:Function.Injective x) (hxA:∀ i,x i∉A)
    (hM:∀ i,OrdinaryRowCover (M i) (x i) A K)
    (hcross:∀ i j,i≠j→Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)):
    ∃ N:Fin n→Finset (OrdinaryWheel Q F H r),
      (∀ i,N i⊆M i) ∧ (∀ i,OrdinaryRowCover (N i) (x i) A K) ∧
      (∀ i j,i≠j→Disjoint ((N i).biUnion ordinaryWheelResources) ((N j).biUnion ordinaryWheelResources)) ∧
      (∀ i,∀ W∈N i,∀ k,x k∈(ordinaryWheelRim W).support ↔ k=i) ∧
      (∀ a∈A,(ordinaryWheelRimGraph (Finset.univ.biUnion N)).degree a≤n*(2*(K+1))) ∧
      (∀ a∈A,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion N) a)).card≤n*(K+1)) ∧
      (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion N) a u)).card≤n*r):=by
  let N:=fun i=>(M i).filter (fun W=>x i∈(ordinaryWheelRim W).support)
  have hNM (i:Fin n):N i⊆M i:=Finset.filter_subset _ _
  have hc (i:Fin n):OrdinaryRowCover (N i) (x i) A K:=(hM i).filter_root
  refine ⟨N,hNM,hc,?_,?_,row_cover_union_degree_bounds N x A hxA hc⟩
  · intro i j hij
    apply (hcross i j hij).mono
    · intro e he
      obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨W,hNM i hW,he⟩
    · intro e he
      obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨W,hNM j hW,he⟩
  · intro i W hW k
    constructor
    · intro hk
      rcases (hM i).support W (hNM i hW) (x k) hk with he|ha
      · exact hx he
      · exact (hxA k ha).elim
    · rintro rfl
      exact (Finset.mem_filter.mp hW).2

end Oberwolfach
