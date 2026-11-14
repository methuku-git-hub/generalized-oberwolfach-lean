module

public import Oberwolfach.MarkedDecompositionPermutationDirected

@[expose] public section
/-! A marked-wheel resource decomposition supplies the simple walks needed on
 the already fixed buffered source paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_decomposition_supplies_buffered_walks
    {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V) (m b d:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (H₀ Hₖ:V→U→Prop)
    (hdec:HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ))
      (markedDecompositionTarget (markedPhysicalRimSet tail head ktail khead π) H₀ Hₖ))
    (J:U→Type) [∀u,Fintype (J u)] (a:∀u,J u→V)
    (hinj:∀u j,Function.Injective (fun i:Fin (d+1)=>(π^i.val) (a u j)))
    (hdis:∀u (j l:J u),j≠l→Disjoint (permutationWindow π 0 d (a u j)) (permutationWindow π 0 d (a u l)))
    (hend:∀u j,(π^d) (a u j)∉Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))
    (hmarked:∀u x,Hₖ x u↔x∈markedIntervalRootSet π (fun _:J u=>d) (a u))
    (hsep:∀u x,Hₖ x u→¬H₀ x u)
    (hloopE:∀e:E,tail e≠head e) (hloopK:∀e:K,ktail e≠π (khead e))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    let G:=physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)
    ∃start finish:∀u,J u→V,
      (∀u j,start u j=a u j) ∧ (∀u j,finish u j=(π^d) (a u j)) ∧
    ∃q:∀u (j:J u),G.Walk (start u j) (finish u j),
      (∀u j,(q u j).IsPath) ∧ (∀u j,(q u j).length=(m+1)*d) ∧
      (∀u j l,j≠l→Disjoint (q u j).support.toFinset (q u l).support.toFinset) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>(q u j).support.toFinset))=
        (Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) ∪ Finset.univ.image (finish u)) ∧
      (∀u w,u≠w→∀j:J u,∀l:J w,Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q w l))):=by
  intro G
  obtain ⟨v,hv0,hvlast,C,q,hpath,hvertices,hcover,hedges,hcross,hrest⟩:=
    marked_decomposition_permutation_reconstruction_directed tail head ktail khead m b π hb H₀ Hₖ hdec J (fun _ _=>d) a
      hinj hdis hend hmarked hsep hloopE hloopK hphysical
  refine ⟨(fun u j=>v u j 0),(fun u j=>v u j (Fin.last d)),hv0,hvlast,q,?_,?_,hvertices,hcover,hcross⟩
  · exact fun u j=>(hpath u j).1
  · intro u j
    simpa only [Nat.mul_comm] using (hpath u j).2
end Oberwolfach
