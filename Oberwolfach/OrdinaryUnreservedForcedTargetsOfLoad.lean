module

public import Oberwolfach.OrdinaryUnreservedForcedTargets
public import Oberwolfach.OrdinaryUnreservedSampledLoadEventually

@[expose] public section
/-! On the same expanded outcome, the occupancy event supplies the actual
unreserved prescribed-image load for simultaneous residual placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assignment_unreserved_placement_forced_targets_of_load
    (δ:ℝ) (hδ:0<δ):
    ∀(m:ℕ),∀{n:ℕ},∀{U:Type} [Fintype U] [DecidableEq U]
    {J:U→Type} [∀u,DecidableEq (J u)]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (a:ℝ) (hEvent:OrdinaryProtectedBadEdgeAssignments π d σ a)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (G Jbad:SimpleGraph (Fin n)) (Dstar Dfree:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (hDD:∀x y,Dfree x y→Dstar x y)
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent),
    let σI:=fun e=>σ (Sum.inr e)
    let A:=fun u=>retainedMarkedIndex π d σI false t Jret u
    let B:=fun u=>{x:Fin n // rawIntervalColouredStart π d (fun e=>σI (u,e)) x true}
    let X:=fun u=>{x:Fin n // (F₀ u).connectedComponentMk x∉Cres u}
    let H:=fun u=>(F₀ u).induce {x | (F₀ u).connectedComponentMk x∉Cres u};
    ∀(data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (H u))
    (ext:∀u,A u⊕B u→Fin ((m+1)*d+5)↪X u)
    (inner:∀u,A u→Fin ((m+1)*d+1)↪X u)
    (hc:∀u,(data u).c=m+1) (hd:∀u,(data u).d=d)
    (hs:∀u,(data u).s₁=firstSumIndices)
    (hsupp:∀u i,((data u).P i).support=List.ofFn (ext u i))
    (hinner:∀u i k,inner u i k=ext u (.inl i) ⟨k.val+2,by omega⟩)
    (hC:∀u,(data u).Cembed=(data u).t.biUnion (fun j=>((data u).C j).support.toFinset))
    (Old:∀u,Finset (X u))
    (hOldEq:∀u,Old u=(data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>(m+1)*d) (inner u))
    (ψ:∀u,X u→Fin n)
    (hmarker:∀u i (j:Fin (d+1)),bufferedMarker (m+1) d (ext u i) j∈(data u).prescribed→
      ψ u (bufferedMarker (m+1) d (ext u i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σI false true t Jret u i))
    (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (hOld:∀u,Disjoint ((Old u).image (ψ u))
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u))
    (T:U→Finset (Fin n)) (Inner:Finset (Fin n)) (Protected:Finset U)
    (hT:∀u,T u⊆Inner) (hTsupport:∀u,T u≠∅→u∈Protected)
    (hProtected:((Protected.card:ℝ))≤δ*n/2)
    (b:ℝ) (hb:0≤b) (hbsmall:b≤a/16) (hbδ:b≤δ/8) (hdegree:∀v,(G.degree v:ℝ)≤b*n)
    (hcapacity:∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊+4*Inner.card+10≤Fintype.card {x // x∈(data u).remaining})
    (β:ℝ) (hβ:0<β) (hβ1:β≤1) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(n:ℝ)) (hn:2/Real.sqrt δ≤(n:ℝ)) (hU:Fintype.card U≤n)
    (hsize:∀u,(Fintype.card {x // x∈(data u).remaining}:ℝ)≤δ*n)
    (hload:∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v≤δ*n/2)
    (hJ:∀v,(Jbad.degree v:ℝ)≤δ*n)
    (hext:∀u,IsExtendingList Dfree
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) β),
    ∃(D:∀u,X u→X u→Prop) (pieces:∀u,List (PrescribedSourcePiece {x // x∈(data u).remaining}))
      (M:U→Finset (Fin n×Fin n))
      (B:∀u,Finset {x // x∈(data u).remaining})
      (g Φ:∀u,{x // x∈(data u).remaining}→Fin n),
      (∀u,prescribedDependentGraph pieces u=((data u).graph).induce (fun x=>x∈(data u).remaining)) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y ↔ D u x.1 y.1 ∧ (data u).graph.Adj x.1 y.1) ∧
      (∀u,IsPrescribedOrientedMatching (M u)) ∧
      (∀u,Disjoint ((Old u).image (ψ u)) (prescribedMatchingEndpoints (M u))) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      (∀u,Function.Injective (Φ u)) ∧
      (∀u,residualSubtypeSet (data u).remaining (data u).prescribed⊆B u ∧
        (∀x∈residualSubtypeSet (data u).remaining (data u).prescribed,g u x=ψ u x.1) ∧
        (B u).image (g u)=
          (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪
            prescribedMatchingEndpoints (M u)∪
            ((T u\(Old u).image (ψ u))\prescribedMatchingEndpoints (M u)) ∧
        (prescribedInducedArcs (prescribedDependentDigraph pieces u) (B u)).image (Prod.map (g u) (g u))=M u) ∧
      (∀u v,v∈T u→v∈(Old u).image (ψ u) ∨ ∃x,Φ u x=v) ∧
      (∀u x,x∈B u→Φ u x=g u x) ∧
      (∀u x,x∉B u→Φ u x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y→Dstar (Φ u x) (Φ u y) ∧
        ((x∉B u ∨ y∉B u)→Dfree (Φ u x) (Φ u y))) ∧
      let E:U→Finset (Sym2 (Fin n)):=fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u));
      PairwisePhysicalDisjoint E ∧ (∀u,(M u).image prescribedArcPhysical⊆E u) ∧
      (∀e∈G.edgeFinset,∃u,e∈E u) ∧
      (∀u,Disjoint (E u\(M u).image prescribedArcPhysical) Jbad.edgeFinset) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*n)  :=by
  intro m n U _ _ J _ π d σ a hEvent t Jret G Jbad Dstar Dfree hDstar hDD F₀ hF₀ Cres σI A B X H data ext inner hc hd hs hsupp hinner hC Old hOldEq ψ hmarker hψ hOld T Inner Protected hT hTsupport hProtected b hb hbsmall hbδ hdegree hcapacity β hβ hβ1 hδbound hnβ hn' hU hsize hload hJ hext
  have hTload:∀v,((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤Protected.card:=by
    intro v
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
    apply hTsupport u
    intro he
    have hm: v∈T u:=(Finset.mem_sdiff.mp hu).1
    simpa [he] using hm
  have hload':∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤δ*n:=by
    intro v
    have hh:=hload v
    have ht:=hTload v
    linarith
  have hcap':∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊+4*((T u\(Old u).image (ψ u)).card)+10≤Fintype.card {x // x∈(data u).remaining}:=by
    intro u
    have hh:=hcapacity u
    have ht:((T u\(Old u).image (ψ u)).card)≤Inner.card:=Finset.card_le_card ((Finset.sdiff_subset).trans (hT u))
    omega
  exact ordinary_assignment_unreserved_buffered_residual_placement_forced_targets π d σ a hEvent t Jret G Jbad Dstar Dfree hDstar hDD F₀ hF₀ Cres (m+1)
    data ext inner hc hd hs hsupp hinner hC Old hOldEq ψ hψ hOld T b hb hbsmall hdegree hcap' β δ hβ hβ1 hδ hδbound hnβ hn' hU hsize hload' hJ hext
end Oberwolfach
