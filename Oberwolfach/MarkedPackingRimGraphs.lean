module

public import Oberwolfach.MarkedFactorPhysical
public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! The actual physical rim graph of a finite marked wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def markedPackingRims (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)):Finset (Finset V):=
  M.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1)

def markedPackingRimGraph (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)):SimpleGraph V:=
  physicalEdgeGraph (markedPackingRims M)

theorem markedPackingRimGraph_empty:
    markedPackingRimGraph (∅:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))=⊥:=by
  ext x y
  simp [markedPackingRimGraph,markedPackingRims,physicalEdgeGraph]

theorem markedPackingRimGraph_biUnion {n:ℕ} (C:Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)):
    markedPackingRimGraph (Finset.univ.biUnion C)=⨆ i,markedPackingRimGraph (C i):=by
  ext x y
  simp only [markedPackingRimGraph,physicalEdgeGraph,markedPackingRims,SimpleGraph.iSup_adj,
    Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hne,W,⟨i,hWi⟩,he⟩
    exact ⟨i,hne,W,hWi,he⟩
  · rintro ⟨i,hne,W,hWi,he⟩
    exact ⟨hne,W,⟨i,hWi⟩,he⟩

theorem graph_adj_of_physical_pair_eq (D:SimpleGraph V) (a c x y:V)
    (he:({a,c}:Finset V)={x,y}) (hxy:D.Adj x y):D.Adj a c:=by
  have ha:a=x∨a=y:=by have hh:a∈({x,y}:Finset V):=he ▸ (by simp);simpa using hh
  rcases ha with ha|ha
  · rw [ha] at he ⊢
    have hy:y=x∨y=c:=by have hh:y∈({x,c}:Finset V):=he.symm ▸ (by simp);simpa using hh
    rcases hy with h|h
    · exact (hxy.ne h.symm).elim
    · exact h ▸ hxy
  · rw [ha] at he ⊢
    have hx:x=y∨x=c:=by have hh:x∈({y,c}:Finset V):=he.symm ▸ (by simp);simpa using hh
    rcases hx with h|h
    · exact (hxy.ne h).elim
    · exact h ▸ hxy.symm

theorem marked_cycle_rim_avoids_deleted_graph (D:SimpleGraph V)
    (C:MarkedCycleTuple (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) m π b)
    (x y:V) (he:({x,y}:Finset V)∈markedCyclePhysicalEdges
      (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) m π b C):
    ¬D.Adj x y:=by
  intro hxy
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
  simp only [Function.comp_apply] at hi
  generalize markedCycleTypedEdge _ _ _ _ m π b C i=a at hi
  cases a with
  | inl e=>exact e.property (graph_adj_of_physical_pair_eq D _ _ x y hi hxy)
  | inr e=>exact e.property (graph_adj_of_physical_pair_eq D _ _ x y hi hxy)

theorem marked_packing_distinct_hubs_disjoint
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (u v:U) (huv:u≠v)
    (hM:∀ W∈M,W.2.val=u) (hN:∀ W∈N,W.2.val=v)
    (hpairs:∀ e∈markedPackingRims M,e.card=2)
    (hgraphs:Disjoint (markedPackingRimGraph M) (markedPackingRimGraph N)):
    Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
  obtain ⟨Z,hZ,hf⟩:=Finset.mem_biUnion.mp hf
  cases e with
  | inr e=>
    rw [markedWheelPhysicalResources_spoke] at he hf
    exact huv ((hM W hW).symm.trans (he.1.trans (hf.1.symm.trans (hN Z hZ))))
  | inl e=>
    rw [markedWheelPhysicalResources_rim] at he hf
    have hMe:e∈markedPackingRims M:=Finset.mem_biUnion.mpr ⟨W,hW,he⟩
    have hNe:e∈markedPackingRims N:=Finset.mem_biUnion.mpr ⟨Z,hZ,hf⟩
    obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp (hpairs e hMe)
    exact disjoint_graphs_no_common_edge _ _ hgraphs x y ⟨hxy,hMe⟩ ⟨hxy,hNe⟩

end Oberwolfach
