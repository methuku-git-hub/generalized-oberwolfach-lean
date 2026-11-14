module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage

@[expose] public section
/-! Construct a coherent per-hub placement package from the actual packed
paths and cycles, retaining the original directed and physical cover facts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_residual_package_from_packing
    {X V U E L A B J W:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq U]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
    (G:SimpleGraph X) (m d:ℕ) (hm:3≤m+1) (hd:0<d) (π:Equiv.Perm V) (targetRoot:A⊕B→V)
    (ext:A⊕B→Fin ((m+1)*d+5)↪X) (inner:A→Fin ((m+1)*d+1)↪X)
    (P:∀i,G.Walk (ext i 0) (ext i (Fin.last ((m+1)*d+4))))
    (hp:∀i,(P i).IsPath) (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hlen:∀i,(P i).length=(m+1)*d+4)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (hinner:∀i k,inner i k=ext (.inl i) ⟨k.val+2,by omega⟩)
    (root:J→X) (C:∀j,G.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset)
    (len:J→ℕ) (hClen:∀j,(C j).length=len j)
    (tail head:E→V) (ktail khead:L→V) (b:ℕ) (H₀ Hₖ:V→U→Prop) (hub:U)
    (marks:W→Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (Good:W→Prop) (Pack:W→Finset (Finset V)) (marker:W) (hGood:Good marker)
    (ψ:X→V) (Arc:V→V→Prop) (Avail Reserve:Finset V):
    let data:=actualResidualDataFromPacking G (fun i=>ext i 0) (fun i=>ext i (Fin.last ((m+1)*d+4)))
      P hp hP (m+1) d hm hd hlen tail head ktail khead m b π H₀ Hₖ (marks marker) hub targetRoot root C hcycle hC hcross;
    (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext i) j∈data.prescribed→
      ψ (bufferedMarker (m+1) d (ext i) j)=(π^j.val) (targetRoot i))→
    Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) inner):Set X)→
    Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) inner).image ψ) Avail→
    Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) inner).image ψ) Reserve→
    ActualOldImageDirected data ψ Arc→ActualOldPhysicalCoverage data ψ (Pack marker)→
    (∀edge∈Pack marker,∃e:Sym2 V,e∈data.deletedEdges.image (Sym2.map ψ) ∧ e.toFinset=edge)→
    Nonempty (OrdinaryMatchedResidualHubPackage G m d π targetRoot Arc Avail Reserve Good Pack
      (fun w i=>packedPhysicalSpokePositions tail head ktail khead m b d π H₀ Hₖ (marks w) hub (targetRoot (.inr i))) len) :=by
  intro data hmarker hinj havoid hreserve hdir hcover hrims
  refine ⟨⟨marker,hGood,data,ext,inner,ψ,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,hsupp,hinner,hmarker,hinj,havoid,hreserve,hdir,hcover,hrims⟩⟩
  · exact hClen
  · intro i
    rfl
end Oberwolfach
