module

public import Oberwolfach.MarkedDecompositionIndexedDirected
public import Oberwolfach.MarkedPermutationIntervalGeometryInjective

@[expose] public section
/-! Reconstruct all prescribed intervals from a physical marked-wheel packing,
with hubwise vertex partitions and a global physical-rim edge partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_decomposition_permutation_reconstruction_directed
    {V U E K:Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V→U→Prop)
    (hdec:HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ))
      (markedDecompositionTarget (markedPhysicalRimSet tail head ktail khead π) H₀ Hₖ))
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
      Finset.univ.biUnion (fun u:U=>Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=
        markedPhysicalRimSet tail head ktail khead π ∧
      (∀u (j l:J u),j≠l→Disjoint (walkPhysicalArcs (q u j)) (walkPhysicalArcs (q u l))) ∧
      (∀u w:U,u≠w→∀j:J u,∀l:J w,Disjoint (walkPhysicalArcs (q u j)) (walkPhysicalArcs (q w l))) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>walkPhysicalArcs (q u j)))=(M u).biUnion (fun C=>
        markedCyclePhysicalArcs tail head ktail khead m π b (hubCycleAsMarked u C))) ∧
      (∀u,(Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)).card=(m+1)*(Y u).card) ∧
      Finset.univ.biUnion (fun u:U=>Finset.univ.biUnion (fun j:J u=>walkPhysicalArcs (q u j)))=
        Finset.univ.image (markedPhysicalArc tail head ktail khead π) := by
  let Y:U→Finset V:=fun u=>markedIntervalRootSet π (k u) (a u)
  have hexist:∀u:U,∃v:∀j:J u,Fin (k u j+1)↪V,
      (∀j,v j 0=a u j) ∧ (∀j,v j (Fin.last (k u j))=(π^(k u j)) (a u j)) ∧
      (∀j (i:Fin (k u j)),v j i.castSucc∈Y u) ∧
      (∀j (i:Fin (k u j)),π (v j i.castSucc)=v j i.succ) ∧
      (∀j,v j (Fin.last (k u j))∉Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) ∧
      (∀j l:J u,j≠l→∀i:Fin (k u j),∀t:Fin (k u l),v j i.castSucc≠v l t.castSucc) ∧
      (∀x∈Y u,∃j:J u,∃i:Fin (k u j),v j i.castSucc=x) ∧
      (∀j l:J u,j≠l→v j (Fin.last (k u j))≠v l (Fin.last (k u l))):=by
    intro u
    exact marked_permutation_interval_geometry_of_injective π (k u) (a u)
      (Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) (hinj u) (hdis u) (hend u)
  let v:∀u j,Fin (k u j+1)↪V:=fun u=>Classical.choose (hexist u)
  have hv:=fun u=>Classical.choose_spec (hexist u)
  obtain ⟨M,q,hpath,hvertices,hvertexcover,hedges,hcross,hhubedges,hglobal,harcs,harccross,harcHub,hcount,harcGlobal⟩:=
    marked_decomposition_indexed_reconstruction_directed tail head ktail khead m b π hb H₀ Hₖ hdec Y hmarked hsep J k v
      (fun u=>(hv u).2.2.1) (fun u=>(hv u).2.2.2.1) (fun u=>(hv u).2.2.2.2.1)
      (fun u=>(hv u).2.2.2.2.2.1) (fun u=>(hv u).2.2.2.2.2.2.1) (fun u=>(hv u).2.2.2.2.2.2.2)
      hloopE hloopK hphysical
  exact ⟨v,(fun u=>(hv u).1),(fun u=>(hv u).2.1),M,q,hpath,hvertices,hvertexcover,hedges,hcross,hhubedges,hglobal,harcs,harccross,harcHub,hcount,harcGlobal⟩
end Oberwolfach
