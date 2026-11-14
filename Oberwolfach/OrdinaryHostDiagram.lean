module

public import Oberwolfach.OrdinaryFiveHostEmbeddings
public import Oberwolfach.OrdinaryFourDiagramInputs
public import Oberwolfach.OrdinaryFiveGraphGeometry
public import Oberwolfach.OrdinaryActualDiagramOrders
public import Oberwolfach.OrdinaryAttachmentForbiddenResources

@[expose] public section

/-! A constructed five-graph diagram in the actual host. Its finite
maps, physical-edge partitions, endpoint bounds and exclusions are proved
from the original remainder and the host neighbourhood hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryHostDiagram (r M:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (original:Finset (Sym2 V⊕(V×U))) (A W R₀:Finset V) (B₀ O:Finset U) where
  rows : Finset V
  hubs : Finset U
  rows_card : rows.card≤5*M
  hubs_card : hubs.card≤5*M
  rows_location : rows⊆R₀∪A
  rows_avoid : ∀ v∈rows,v∈W→v∈R₀
  hubs_avoid : ∀ u∈hubs,u∈B₀→u∈O
  D : Fin 5→Finset (Sym2 V⊕(V×U))
  disjoint : ∀ i j,i≠j→Disjoint (D i) (D j)
  Drows : ∀ i,ordinaryResourceRows (D i)⊆rows
  Dhubs : ∀ i,ordinaryResourceHubs (D i)⊆hubs
  host : ∀ i,D i⊆ordinaryHostResources Q H
  avoid : ∀ i,i≠0→Disjoint (D i) (ordinaryRootResources (R₀∪W) B₀)
  extra : Finset (Sym2 V⊕(V×U))
  first : D 0=original∪extra
  first_disjoint : Disjoint original extra
  extra_decomp : HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) extra
  extra_avoid : Disjoint extra (ordinaryRootResources (R₀∪W) B₀)
  last_decomp : HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (D 4)
  T : Fin 4→OrdinaryTransformerInput r (5*M) Q F H rows (B₀∪hubs)
  source : ∀ j,ordinaryHostResources (T j).G (T j).K=![D 1,D 1,D 3,D 3] j
  target : ∀ j,transformerImageResources (T j).G (T j).K (T j).φ (T j).ψ=![D 0,D 2,D 2,D 4] j

variable {V₀ U₀:Type} [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]

theorem ordinary_host_diagram (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop)
    (r m:ℕ) (hr:3≤r) (hm:Fintype.card V₀+Fintype.card U₀≤m)
    (hbal:∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀ u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)
    (Q F:SimpleGraph V) (H:V→U→Prop) (A W R₀:Finset V) (B₀:Finset U)
    (φ:V₀↪V) (ψ:U₀↪U) (hφ:∀ v,φ v∈R₀) (hψ:∀ u,ψ u∈B₀)
    (hG:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w)) (hHs:∀ v u,Hs v u→H (φ v) (ψ u))
    (hQF:∀ v w,Q.Adj v w→¬F.Adj v w)
    (d c cH:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hA:c≤(A.card:ℝ)) (hU:cH≤(Fintype.card U:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair:∀ a b v w,c≤(((A.filter (fun z=>H z a∧H z b))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R₀.card:ℝ)+6*ordinaryDiagramSize r m+r+6)*(d+1)<c)
    (hB:(B₀.card:ℝ)+6*ordinaryDiagramSize r m<cH) :
    Nonempty (OrdinaryHostDiagram r (ordinaryDiagramSize r m) Q F H
      (ordinaryHostResources (G.map φ) (ordinaryMappedSpokes Hs φ ψ)) A W R₀ B₀ (Finset.univ.image ψ)) := by
  obtain ⟨eL,hLf,hLg,hLpriv,hLhub,extra,hpart,hpartdis,hextra,eR,hRfresh,hRdec,e,hefresh,hedv,hedu,heseparate⟩:=
    ordinary_five_host_embeddings G Hs r m hr hm Q F H A W R₀ B₀ φ ψ hφ hψ hG hHs d c cH hd hF hA hU hcount hpair hhub hbudget hB
  let rows:=ordinaryFiveUnion (Finset.univ.image eL.row) (Finset.univ.image eR.row) (fun i=>Finset.univ.image (e i).row)
  let hubs:=ordinaryFiveUnion (Finset.univ.image eL.hub) (Finset.univ.image eR.hub) (fun i=>Finset.univ.image (e i).hub)
  have hLR:∀ a,eL.row a∈rows:=fun a=>ordinaryFiveUnion_left _ _ _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have hRR:∀ a,eR.row a∈rows:=fun a=>ordinaryFiveUnion_right _ _ _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have heR:∀ i a,(e i).row a∈rows:=fun i a=>ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).row) i (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have hLB:∀ a,eL.hub a∈hubs:=fun a=>ordinaryFiveUnion_left _ _ _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have hRB:∀ a,eR.hub a∈hubs:=fun a=>ordinaryFiveUnion_right _ _ _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have heB:∀ i a,(e i).hub a∈hubs:=fun i a=>ordinaryFiveUnion_mid _ _ (fun j=>Finset.univ.image (e j).hub) i (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have orders:=ordinary_actual_diagram_orders G Hs r m hr hm
  have hrows:rows.card≤5*ordinaryDiagramSize r m:=by
    apply ordinaryFiveUnion_card
    · rw [eL.row_card];exact (Nat.le_add_right _ _).trans orders.1
    · rw [eR.row_card];exact (Nat.le_add_right _ _).trans orders.2.1
    · intro i;rw [(e i).row_card];exact (Nat.le_add_right _ _).trans (orders.2.2 i)
  have hhubs:hubs.card≤5*ordinaryDiagramSize r m:=by
    apply ordinaryFiveUnion_card
    · rw [eL.hub_card];exact (Nat.le_add_left _ _).trans orders.1
    · rw [eR.hub_card];exact (Nat.le_add_left _ _).trans orders.2.1
    · intro i;rw [(e i).hub_card];exact (Nat.le_add_left _ _).trans (orders.2.2 i)
  obtain ⟨T,hsource,htarget⟩:=ordinary_four_diagram_inputs G Hs r m hr hm hbal hdiv Q F H hQF A W R₀ rows B₀ (B₀∪hubs)
    eL eR e hefresh hedv hedu heseparate hLR hRR heR
    (fun a=>Finset.mem_union_right _ (hLB a)) (fun a=>Finset.mem_union_right _ (hRB a))
    (fun i a=>Finset.mem_union_right _ (heB i a))
  have geometry:=ordinary_five_graph_geometry _ _ _ _ _ _ Q F H eL eR e A W R₀ B₀ hRfresh hefresh hedv
  let D:Fin 5→Finset (Sym2 V⊕(V×U)):=![eL.resources,(e 0).resources,(e 1).resources,(e 2).resources,eR.resources]
  have hRavoid:Disjoint eR.resources (ordinaryRootResources (R₀∪W) B₀):=by
    apply eR.resources_avoid_roots
    intro a ha
    rcases Finset.mem_union.mp ha with h|h
    · exact (hRfresh.1 a).2.2.1 (Finset.mem_union_left _ h)
    · exact (hRfresh.1 a).2.1 h
  have heavoid (i:Fin 3):Disjoint (e i).resources (ordinaryRootResources (R₀∪W) B₀):=by
    apply (e i).resources_avoid_roots
    intro a ha
    rcases Finset.mem_union.mp ha with h|h
    · exact ((hefresh i).1 a).2.2.1 (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    · exact ((hefresh i).1 a).2.1 h
  refine ⟨{
    rows:=rows
    hubs:=hubs
    rows_card:=hrows
    hubs_card:=hhubs
    rows_location:=?_
    rows_avoid:=?_
    hubs_avoid:=?_
    D:=D
    disjoint:=geometry.1
    Drows:=geometry.2.1
    Dhubs:=geometry.2.2.1
    host:=geometry.2.2.2
    avoid:=?_
    extra:=extra
    first:=hpart
    first_disjoint:=hpartdis
    extra_decomp:=hextra
    extra_avoid:=?_
    last_decomp:=hRdec
    T:=T
    source:=hsource
    target:=htarget }⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
        cases a with
        | inl a=>rw [hLf];exact Finset.mem_union_left _ (hφ a)
        | inr p=>exact Finset.mem_union_right _ (hLpriv p.1 p.2).1
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
        exact Finset.mem_union_right _ (hRfresh.1 a).1
    · obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
      exact Finset.mem_union_right _ ((hefresh i).1 a).1
  · intro v hv hvW
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
        cases a with
        | inl a=>rw [hLf];exact hφ a
        | inr p=>exact ((hLpriv p.1 p.2).2.1 hvW).elim
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
        exact ((hRfresh.1 a).2.1 hvW).elim
    · obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hv
      exact (((hefresh i).1 a).2.1 hvW).elim
  · intro u hu huB
    rcases Finset.mem_union.mp hu with hu|hu
    · rcases Finset.mem_union.mp hu with hu|hu
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hu
        cases a with
        | inl a=>rw [hLg];exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
        | inr a=>exact (hLhub a huB).elim
      · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hu
        exact (hRfresh.2.1 a (Finset.mem_union_left _ huB)).elim
    · obtain ⟨i,_,hu⟩:=Finset.mem_biUnion.mp hu
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hu
      exact ((hefresh i).2.1 a (Finset.mem_union_left _ (Finset.mem_union_left _ huB))).elim
  · intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact heavoid 0
    · exact heavoid 1
    · exact heavoid 2
    · exact hRavoid
  · exact ordinary_attachment_forbidden_resources G Hs (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ (actualAttachmentRoot G Hs)
      φ ψ eL.row eL.hub hLf hLg (R₀∪W) B₀
      (by intro i w h;rcases Finset.mem_union.mp h with h|h
          · exact (hLpriv i w).2.2.1 h
          · exact (hLpriv i w).2.1 h)
      hLhub extra hpart hpartdis

end Oberwolfach
