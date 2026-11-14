module

public import Oberwolfach.MarkedDecompositionEdgeDisjointPartialMapsCounts
public import Oberwolfach.LongReservedCapacityFromRpow

@[expose] public section
/-! Derive the reserved-path capacities in the marked factor-map construction
from the manuscript's long-cycle and fourth-root numerical hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem marked_decomposition_to_edge_disjoint_maps_with_rpow_capacity
    {X V U E K:Type*} [Fintype X] [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq X] [DecidableEq V] [DecidableEq U]
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
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (F:U→SimpleGraph X) (hF:∀u,(F u).IsRegularOfDegree 2)
    (I:U→Type*) [∀u,Fintype (I u)]
    (components:∀u,I u↪(F u).ConnectedComponent)
    (e:∀u (i:I u),SimpleGraph.cycleGraph (Fintype.card (components u i)) ≃g (components u i).toSimpleGraph)
    (d:ℕ) (hk:∀u j,k u j≤d)
    (hd:0<d) (B:ℕ) (hB:0<B) (N θ:ℝ) (ell:U→ℝ)
    (hN:0<N) (hθ:0<θ) (hell:∀u,(1:ℝ)/2≤ell u)
    (hmin:∀u (i:I u),B≤Fintype.card (components u i))
    (htotal:∀u,((∑i:I u,Fintype.card (components u i):ℕ):ℝ)=ell u*N)
    (hcut:5/(((m+1:ℕ):ℝ)*(d:ℝ)+5)+((m+1:ℕ):ℝ)*(d:ℝ)/B≤θ/2)
    (hlarge:8*((m+1:ℕ):ℝ)/θ<N^((1:ℝ)/4))
    (hdemand:∀u,(Fintype.card (J u):ℝ)≤(1-θ)*ell u*N/(((m+1:ℕ):ℝ)*(d:ℝ))+
      2*N^((3:ℝ)/4)/(d:ℝ)):
    let G:=physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)
    let Y:U→Finset V:=fun u=>markedIntervalRootSet π (k u) (a u)
    ∃v:∀u j,Fin (k u j+1)↪V,
      (∀u j,v u j 0=a u j) ∧ (∀u j,v u j (Fin.last (k u j))=(π^(k u j)) (a u j)) ∧
    ∃M:∀u:U,Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u),
    ∃q:∀u (j:J u),G.Walk (v u j 0) (v u j (Fin.last (k u j))),
      ∃hpath:∀u j,(q u j).IsPath ∧ (q u j).length=k u j*(m+1),
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
        Finset.univ.image (markedPhysicalArc tail head ktail khead π) ∧
    ∃index:∀u,J u↪LongReservedBlockIndex (F u) (components u) (m+1) d,
    ∃ext:∀u (j:J u),Fin ((m+1)*k u j+5)↪X,
    ∃inner:∀u (j:J u),Fin ((m+1)*k u j+1)↪X,
    ∃φ:∀u,{x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))}↪V,
      (∀u j,ext u j=longReservedSigmaBlock (F u) (components u) (m+1) d (e u) (index u j) (k u j) (hk u j)) ∧
      (∀u j (i:Fin ((m+1)*k u j+1)),inner u j i=ext u j ⟨i.val+2,by omega⟩) ∧
      (∀u j i,ext u j i∈(components u (index u j).1).supp) ∧
      (∀u (j l:J u),j≠l→Disjoint (Finset.univ.image (ext u j)) (Finset.univ.image (ext u l))) ∧
      (∀u (j:J u),∃p:(F u).Walk (ext u j ⟨0,by omega⟩) (ext u j ⟨(m+1)*k u j+4,by omega⟩),
        p.length=(m+1)*k u j+4 ∧ p.support=List.ofFn (ext u j)) ∧
      (∀u (j:J u) (i:Fin ((m+1)*k u j+1)),
        φ u ⟨inner u j i,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩=
          simpleWalkLengthEmbedding G (q u j) (hpath u j).1 ((m+1)*k u j)
            (by simpa only [Nat.mul_comm] using (hpath u j).2) i) ∧
      (∀u x y,(F u).Adj x.val y.val→G.Adj (φ u x) (φ u y)) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdgesPoly {x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))}
          ((F u).induce (↑(Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))):Set X)) (φ u))
        (partialFactorPhysicalEdgesPoly {x // x∈Finset.univ.biUnion (fun j:J v=>Finset.univ.image (inner v j))}
          ((F v).induce (↑(Finset.univ.biUnion (fun j:J v=>Finset.univ.image (inner v j))):Set X)) (φ v))) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))).card=
        ∑j:J u,((m+1)*k u j+1)) ∧
      (∀u,(Finset.univ\Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))).card=
        Fintype.card X-∑j:J u,((m+1)*k u j+1)) := by
  classical
  have hcapacity:∀u,Fintype.card (J u)≤∑i:I u,Fintype.card (components u i)/((m+1)*d+5) := by
    intro u
    exact long_reserved_capacity_from_rpow (fun i:I u=>Fintype.card (components u i)) (m+1) d B
      (Fintype.card (J u)) N (ell u) θ (by omega) hd hB hN hθ (hell u) (hmin u)
      (htotal u) hcut hlarge (hdemand u)
  exact marked_decomposition_to_edge_disjoint_reserved_partial_maps_with_counts tail head ktail khead m b π hb H₀ Hₖ hdec J k a hinj hdis hend hmarked hsep hloopE hloopK hphysical F hF I components e d hk hcapacity
end Oberwolfach
