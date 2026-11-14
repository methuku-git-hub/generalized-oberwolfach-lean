module

public import Oberwolfach.MarkedDecompositionPackingBridge
public import Oberwolfach.MarkedPackingVertexCount

@[expose] public section
/-! Reconstruct all prescribed intervals from a physical marked-wheel packing,
with hubwise vertex partitions and a global physical-rim edge partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_decomposition_interval_reconstruction
    {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V→U→Prop)
    (Rim:Finset (Finset V))
    (hdec:HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ)) (markedDecompositionTarget Rim H₀ Hₖ))
    (Y:U→Finset V) (hmarked:∀u x,Hₖ x u↔x∈Y u) (hsep:∀u x,Hₖ x u→¬H₀ x u)
    (J:U→Type*) [∀u,Fintype (J u)] (k:∀u,J u→ℕ) (v:∀u j,Fin (k u j+1)↪V)
    (hroots:∀u j (i:Fin (k u j)),v u j i.castSucc∈Y u)
    (hnext:∀u j (i:Fin (k u j)),π (v u j i.castSucc)=v u j i.succ)
    (hend:∀u j,v u j (Fin.last (k u j))∉Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))
    (hrootdis:∀u (j l:J u),j≠l→∀i:Fin (k u j),∀t:Fin (k u l),v u j i.castSucc≠v u l t.castSucc)
    (hYcover:∀u x,x∈Y u→∃j:J u,∃i:Fin (k u j),v u j i.castSucc=x)
    (hendDistinct:∀u (j l:J u),j≠l→v u j (Fin.last (k u j))≠v u l (Fin.last (k u l)))
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∃M:∀u:U,Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u),
    ∃q:∀u (j:J u),G.Walk (v u j 0) (v u j (Fin.last (k u j))),
      (∀u j,(q u j).IsPath ∧ (q u j).length=k u j*(m+1)) ∧
      (∀u (j l:J u),j≠l→Disjoint (q u j).support.toFinset (q u l).support.toFinset) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>(q u j).support.toFinset))=
        (Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) ∪
          Finset.univ.image (fun j:J u=>v u j (Fin.last (k u j)))) ∧
      (∀u (j l:J u),j≠l→Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q u l))) ∧
      (∀u w:U,u≠w→∀j:J u,∀l:J w,Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q w l))) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=(M u).biUnion (hubCyclePhysicalEdges u)) ∧
      (∀u,(Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)).card=(m+1)*(Y u).card) ∧
      Finset.univ.biUnion (fun u:U=>Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=Rim := by
  obtain ⟨P,hP,hspoke,hRim⟩:=marked_decomposition_packing_bridge Rim hdec
  obtain ⟨M,q,hpath,hvertices,hvertexcover,hedges,hcross,hhubedges,hglobal⟩:=
    marked_packing_interval_reconstruction G tail head ktail khead m b π hb H₀ Hₖ P hP hspoke Y hmarked hsep
      J k v hroots hnext hend hrootdis hYcover hendDistinct hE hK hphysical
  have hcount:=marked_packing_hub_vertex_count P hP hspoke Y hmarked hsep
  exact ⟨M,q,hpath,hvertices,hvertexcover,hedges,hcross,hhubedges,hcount,hglobal.trans hRim⟩
end Oberwolfach
