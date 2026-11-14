module

public import Oberwolfach.OrdinaryComplementReferencePhysicalEdit
public import Oberwolfach.MarkedSpokeChangesFromLoss

@[expose] public section
/-! A complement may use some reference spokes.  Their row and column losses
are accounted for explicitly when transferring physical edit estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_reference_physical_edit_with_spoke_loss {n q r:ℕ}
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
    (Href:Fin n→Fin q→Prop) (rsv b κ loss e t lossRow lossCol:ℝ)
    (hb:0≤b) (hκ:0≤κ) (hloss:0≤loss)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hUncovered:∀v,(((Sample\Reference)\ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤κ)
    (hUsed:∀v,((Reference⊓ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤loss)
    (hRefBalance:∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)
    (hRefColumns:∀u,|((Finset.univ.filter (fun v=>Href v u)).card:ℝ)-rsv*n|≤t)
    (hLossRow:∀v,((Finset.univ.filter (fun u=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤lossRow)
    (hLossCol:∀u,((Finset.univ.filter (fun v=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤lossCol)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hK:K⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C f)
      (fun v u=>v∉Set.range (f u))):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Lrim:=b+κ+loss
    let Lspoke:=max (2*lossRow+(Lrim+e)/2) (2*lossCol+t);
    ∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K)
        (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤
      Lrim+Lspoke+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card :=by
  intro Q H Lrim Lspoke
  have hEditQ:=ordinary_remainder_reference_edit_bound Target Sample Reference (ordinaryEmbeddedComplements Fs C f)
    hRef b κ loss hEdit hUncovered hUsed
  have hRim:=ordinary_rim_degree_le_reference_add_edits Q Reference Lrim (by
    intro v
    convert hEditQ v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)
  obtain ⟨hbal,_⟩:=ordinary_complement_remainder_balance Target hTarget Fs hFs C hsize f hC hCC
  have hRowSize:∀v,((Finset.univ.filter (H v)).card:ℝ)-((Finset.univ.filter (Href v)).card:ℝ)≤(Lrim+e)/2:=by
    intro v
    have hbal':(Q.degree v:ℝ)=2*((Finset.univ.filter (H v)).card:ℝ):=by
      have hh:=hbal v
      have hh':Q.degree v=2*(Finset.univ.filter (H v)).card:=by
        convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
      exact_mod_cast hh'
    have href:((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))≤e:=(abs_le.mp (hRefBalance v)).2
    have hrim':(Q.degree v:ℝ)≤(Reference.degree v:ℝ)+Lrim:=by
      convert hRim v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    linarith only [hbal',href,hrim']
  have hColSize:∀u,((Finset.univ.filter (fun v=>H v u)).card:ℝ)-
      ((Finset.univ.filter (fun v=>Href v u)).card:ℝ)≤t:=by
    intro u
    have hc:((Finset.univ.filter (fun v=>H v u)).card:ℝ)=rsv*n:=by
      have hh:=(ordinary_reserved_spoke_cardinality (Fs u) (C u) (hsize u) (f u) (fun v=>H v u) (fun _=>Iff.rfl)).1
      have hh':(Finset.univ.filter (fun v=>H v u)).card=r*(C u).card:=by
        convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
      have hhR:((Finset.univ.filter (fun v=>H v u)).card:ℝ)=(r:ℝ)*(C u).card:=by exact_mod_cast hh'
      exact hhR.trans (hCard u)
    have href:-(t)≤((Finset.univ.filter (fun v=>Href v u)).card:ℝ)-rsv*n:=(abs_le.mp (hRefColumns u)).1
    linarith
  have hrow:∀v,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)≤Lspoke:=by
    intro v
    have hDiff:((Finset.univ.filter (Href v)\Finset.univ.filter (H v)).card:ℝ)≤lossRow:=by
      have heq:Finset.univ.filter (Href v)\Finset.univ.filter (H v)=
          Finset.univ.filter (fun u=>Href v u ∧ v∈Set.range (f u)):=by
        ext u
        simp [H]
      rw [heq]
      exact hLossRow v
    rw [changed_card_from_loss_and_size]
    exact (by linarith [hRowSize v] : _≤2*lossRow+(Lrim+e)/2) |>.trans (le_max_left _ _)
  have hcol:∀u,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤Lspoke:=by
    intro u
    have hDiff:((Finset.univ.filter (fun v=>Href v u)\Finset.univ.filter (fun v=>H v u)).card:ℝ)≤lossCol:=by
      have heq:Finset.univ.filter (fun v=>Href v u)\Finset.univ.filter (fun v=>H v u)=
          Finset.univ.filter (fun v=>Href v u ∧ v∈Set.range (f u)):=by
        ext v
        simp [H]
      rw [heq]
      exact hLossCol u
    rw [changed_card_from_loss_and_size]
    exact (by linarith [hColSize u] : _≤2*lossCol+t) |>.trans (le_max_right _ _)
  have hr:∀v,((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤Lrim:=by
    intro v
    have he:changed (Reference.neighborFinset v) (Q.neighborFinset v)=
        Finset.univ.filter (fun w=>Xor (Q.Adj v w) (Reference.Adj v w)):=by
      ext w
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
        SimpleGraph.mem_neighborFinset,Xor]
      tauto
    rw [he]
    exact hEditQ v
  have hL:0≤Lrim:=by dsimp [Lrim];linarith
  have hbase:∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤Lrim+Lspoke:=by
    apply ordinary_physical_edit_from_typed_changes Reference Q Href H Lrim Lspoke hL
    · intro v;convert hr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    · intro v;convert hrow v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    · intro u;convert hcol u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hout:=ordinary_resource_removal_from_reference Reference Q Href H K hK (Lrim+Lspoke)
    (by intro w;convert hbase w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  intro w
  convert hout w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
