module

public import Oberwolfach.OrdinaryMatchedReferenceSpokeLoss
public import Oberwolfach.OrdinaryComplementPhysicalEditWithSpokeLoss

@[expose] public section
/-! The actual old and new edge partition supplies the two spoke-loss
bounds needed by the complement's physical edit estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_complement_physical_edit {n q r:ℕ}
    {A B J:Fin q→Type} [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (Target Sample Reference:SimpleGraph (Fin n)) (hRef:Reference≤Sample)
    (hTarget:Target.IsRegularOfDegree (2*q))
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→Target.Adj (f u x) (f u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (f u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (f v)))
    (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u)
      ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}))
    (hreg:∀u,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).IsRegularOfDegree 2)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (ψ:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}→Fin n)
    (hfold:∀u x,x∈(data u).oldDomain→f u x=ψ u x)
    (Href:Fin n→Fin q→Prop) (Reserve:Fin q→Finset (Fin n))
    (hHref:∀u v,Href v u→v∈Reserve u)
    (hOld:∀u,Disjoint ((data u).oldDomain.image (ψ u)) (Reserve u))
    (New:Fin q→Finset (Sym2 (Fin n)))
    (hpart:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u))∪New u)
    (hpair:PairwisePhysicalDisjoint New)
    (rsv b κ loss e t rowLoss colLoss:ℝ)
    (hb:0≤b) (hκ:0≤κ) (hloss:0≤loss)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hUncovered:∀v,(((Sample\Reference)\ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤κ)
    (hUsed:∀v,((Reference⊓ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤loss)
    (hRefBalance:∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)
    (hRefColumns:∀u,|((Finset.univ.filter (fun v=>Href v u)).card:ℝ)-rsv*n|≤t)
    (hdegree:∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤rowLoss)
    (hRemaining:∀u,((data u).remaining.card:ℝ)≤colLoss)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hK:K⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u))):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Lrim:=b+κ+loss
    let Lspoke:=max (2*rowLoss+(Lrim+e)/2) (2*colLoss+t);
    ∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K)
        (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤
      Lrim+Lspoke+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card :=by
  have hLoss:=ordinary_matched_reference_spoke_loss
    (fun u=>(Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) hreg data hCycle ψ f Href Reserve
    hHref hOld hfold New hpart hpair rowLoss colLoss hdegree hRemaining
  exact ordinary_complement_reference_physical_edit_with_spoke_loss Target Sample Reference hRef hTarget Fs hFs C hsize f hC hCC
    Href rsv b κ loss e t rowLoss colLoss hb hκ hloss hCard hEdit hUncovered hUsed hRefBalance hRefColumns hLoss.1 hLoss.2 K hK
end Oberwolfach
