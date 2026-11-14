module

public import Oberwolfach.ActualResidualDataFromPacking
public import Oberwolfach.ActualOldFamilyHostPacking
public import Oberwolfach.BufferedPathInteriorCompletion
public import Oberwolfach.BufferedMarkerAnchorEmbedding

@[expose] public section
/-! A per-hub package retains one coherent set of residual paths, their old
physical embedding and the marked-rim packing that generated them. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure OrdinaryMatchedResidualHubPackage
    {X V A B J W:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
    (G:SimpleGraph X) (m d:ℕ) (π:Equiv.Perm V) (targetRoot:A⊕B→V)
    (Arc:V→V→Prop) (Avail Reserve:Finset V)
    (Good:W→Prop) (Pack:W→Finset (Finset V)) (Pos:W→B→Finset ℕ) (cycleLength:J→ℕ) where
  marker : W
  hGood : Good marker
  data : ActualResidualData (K:=A⊕B) (J:=J) G
  ext : A⊕B→Fin ((m+1)*d+5)↪X
  inner : A→Fin ((m+1)*d+1)↪X
  ψ : X→V
  hc : data.c=m+1
  hd : data.d=d
  hs₁ : data.s₁=firstSumIndices
  hs₂ : data.s₂=secondSumIndices
  ht : data.t=Finset.univ
  hEmbed : data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset)
  hCycleLength : ∀j,(data.C j).length=cycleLength j
  hPos : ∀i,data.T (.inr i)=Pos marker i
  hSupp : ∀i,(data.P i).support=List.ofFn (ext i)
  hInner : ∀i k,inner i k=ext (.inl i) ⟨k.val+2,by omega⟩
  hMarker : ∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext i) j∈data.prescribed→
    ψ (bufferedMarker (m+1) d (ext i) j)=(π^j.val) (targetRoot i)
  hInjective : Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) inner):Set X)
  hAvoid : Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) inner).image ψ) Avail
  hAvoidReserve : Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) inner).image ψ) Reserve
  hDirected : ActualOldImageDirected data ψ Arc
  hCoverage : ActualOldPhysicalCoverage data ψ (Pack marker)
  hAllRims : ∀edge∈Pack marker,∃e:Sym2 V,e∈data.deletedEdges.image (Sym2.map ψ) ∧ e.toFinset=edge

end Oberwolfach
