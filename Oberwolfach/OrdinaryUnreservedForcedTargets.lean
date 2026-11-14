module

public import Oberwolfach.OrdinaryAssignmentForcedTargets
public import Oberwolfach.OrdinaryUnreservedResidualOldInputs

@[expose] public section
/-! The protected assignment feeds simultaneous placement on the actual
unreserved induced factors, with buffered interiors removed from the old domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assignment_unreserved_buffered_residual_placement_forced_targets
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {A B J:U→Type} [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (a:ℝ) (hEvent:OrdinaryProtectedBadEdgeAssignments π d σ a)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (G Jbad:SimpleGraph (Fin n)) (Dstar Dfree:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (hDD:∀x y,Dfree x y→Dstar x y)
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent) (c:ℕ):
    let X:=fun u=>{x:Fin n // (F₀ u).connectedComponentMk x∉Cres u}
    let H:=fun u=>(F₀ u).induce {x | (F₀ u).connectedComponentMk x∉Cres u};
    ∀(data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (H u))
    (ext:∀u,A u⊕B u→Fin (c*d+5)↪X u)
    (inner:∀u,A u→Fin (c*d+1)↪X u)
    (hc:∀u,(data u).c=c) (hd:∀u,(data u).d=d)
    (hs:∀u,(data u).s₁=firstSumIndices)
    (hsupp:∀u i,((data u).P i).support=List.ofFn (ext u i))
    (hinner:∀u i k,inner u i k=ext u (.inl i) ⟨k.val+2,by omega⟩)
    (hC:∀u,(data u).Cembed=(data u).t.biUnion (fun j=>((data u).C j).support.toFinset))
    (Old:∀u,Finset (X u))
    (hOldEq:∀u,Old u=(data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>c*d) (inner u))
    (ψ:∀u,X u→Fin n) (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (hOld:∀u,Disjoint ((Old u).image (ψ u))
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u))
    (T:U→Finset (Fin n))
    (b:ℝ) (hb:0≤b) (hbsmall:b≤a/16) (hdegree:∀v,(G.degree v:ℝ)≤b*n)
    (hcapacity:∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊+4*((T u\(Old u).image (ψ u)).card)+10≤Fintype.card {x // x∈(data u).remaining})
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(n:ℝ)) (hn:2/Real.sqrt δ≤(n:ℝ)) (hU:Fintype.card U≤n)
    (hsize:∀u,(Fintype.card {x // x∈(data u).remaining}:ℝ)≤δ*n)
    (hload:∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤δ*n)
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
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*n) :=by
  intro X H data ext inner hc hd hs hsupp hinner hC Old hOldEq ψ hψ hOld T b hb hbsmall hdegree hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hU hsize hload hJ hext
  obtain ⟨hreg,hCycle,hPres⟩:=ordinary_unreserved_residual_restricted_old_inputs F₀ hF₀ Cres c d data ext inner hc hd hs hsupp hinner hC
  have hPresOld:∀u,(data u).prescribed⊆Old u:=by
    intro u
    rw [hOldEq u]
    exact hPres u
  exact ordinary_assignment_dependent_residual_placement_forced_targets π d σ a hEvent t Jret G Jbad Dstar Dfree hDstar hDD H hreg data hCycle Old hPresOld ψ hψ hOld T b hb hbsmall hdegree hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hU hsize hload hJ hext
end Oberwolfach
