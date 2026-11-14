module

public import Oberwolfach.MarkedDecompositionInjectiveReconstruction
public import Oberwolfach.MarkedPhysicalHostGraph

@[expose] public section
/-! Reconstruct all prescribed intervals from a physical marked-wheel packing,
with hubwise vertex partitions and a global physical-rim edge partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_decomposition_physical_interval_reconstruction
    {V U E K:Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V→U→Prop)
    (hdec:HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ)) (markedDecompositionTarget (markedPhysicalRimSet tail head ktail khead π) H₀ Hₖ))
    (J:U→Type*) [∀u,Fintype (J u)] (k:∀u,J u→ℕ) (a:∀u,J u→V)
    (hinj:∀u j,Function.Injective (fun i:Fin (k u j+1)=>(π^i.val) (a u j)))
    (hdis:∀u (j l:J u),j≠l→Disjoint (permutationWindow π 0 (k u j) (a u j))
      (permutationWindow π 0 (k u l) (a u l)))
    (hend:∀u j,(π^(k u j)) (a u j)∉Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))
    (hmarked:∀u x,Hₖ x u↔x∈markedIntervalRootSet π (k u) (a u))
    (hsep:∀u x,Hₖ x u→¬H₀ x u)
    (hloopE:∀e:E,tail e≠head e) (hloopK:∀e:K,ktail e≠π (khead e))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    let G:=physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)
    let Y:U→Finset V:=fun u=>markedIntervalRootSet π (k u) (a u)
    ∃v:∀u j,Fin (k u j+1)↪V,
      (∀u j,v u j 0=a u j) ∧ (∀u j,v u j (Fin.last (k u j))=(π^(k u j)) (a u j)) ∧
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
      Finset.univ.biUnion (fun u:U=>Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=markedPhysicalRimSet tail head ktail khead π := by
  have ⟨hE,hK⟩:=marked_physical_host_graph_inputs tail head ktail khead π hloopE hloopK
  exact marked_decomposition_injective_interval_reconstruction
    (physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)) tail head ktail khead m b π hb H₀ Hₖ
    (markedPhysicalRimSet tail head ktail khead π) hdec J k a hinj hdis hend hmarked hsep hE hK hphysical
end Oberwolfach
