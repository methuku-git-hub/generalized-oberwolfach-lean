module

public import Oberwolfach.OrdinaryComplementQuantitativeTransfer
public import Oberwolfach.OrdinaryRemainderReferenceEdits
public import Oberwolfach.OrdinaryPhysicalEditFromTypedChanges
public import Oberwolfach.OrdinaryResourceRemovalEdit

@[expose] public section
/-! A single quantitative transfer from the actual sampled complement to the
reference rim and spokes.  The uncovered and used-reference degrees remain
explicit inputs, to be supplied by the same-sample matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_reference_physical_edit {n q r:ℕ}
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
    (Href:Fin n→Fin q→Prop) (rsv b κ loss e t:ℝ)
    (hb:0≤b) (hκ:0≤κ) (hloss:0≤loss)
    (hAvoid:∀u x,¬Href (f u x) u)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hUncovered:∀v,(((Sample\Reference)\ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤κ)
    (hUsed:∀v,((Reference⊓ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤loss)
    (hRefBalance:∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)
    (hRefColumns:∀u,|((Finset.univ.filter (fun v=>Href v u)).card:ℝ)-rsv*n|≤t)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hK:K⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C f)
      (fun v u=>v∉Set.range (f u))):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Lrim:=b+κ+loss
    let Lspoke:=max ((Lrim+e)/2) t;
    ∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K)
        (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤
      Lrim+Lspoke+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
  intro Q H Lrim Lspoke
  have hquant:=ordinary_complement_quantitative_reference_transfer Target Sample Reference hRef hTarget Fs hFs C hsize f hC hCC
    Href rsv b κ loss e t hAvoid hCard hEdit hUncovered hUsed hRefBalance hRefColumns
  have hr:∀v,((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤Lrim:=by
    intro v
    have he:changed (Reference.neighborFinset v) (Q.neighborFinset v)=
        Finset.univ.filter (fun w=>Xor (Q.Adj v w) (Reference.Adj v w)):=by
      ext w
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
        SimpleGraph.mem_neighborFinset,Xor]
      tauto
    rw [he]
    exact hquant.1 v
  have href:∀v u,Href v u→H v u:=by
    intro v u hv hx
    obtain ⟨x,rfl⟩:=hx
    exact hAvoid u x hv
  have hrow:∀v,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)≤Lspoke:=by
    intro v
    have he:changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))=
        Finset.univ.filter (fun u=>H v u∧¬Href v u):=by
      ext u
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
      have :=href v u
      tauto
    rw [he]
    have hh:=hquant.2.1 v
    have hbnd:((Finset.univ.filter (fun u=>H v u∧¬Href v u)).card:ℝ)≤(Lrim+e)/2:=by linarith
    exact hbnd.trans (le_max_left _ _)
  have hcol:∀u,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤Lspoke:=by
    intro u
    have he:changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))=
        Finset.univ.filter (fun v=>H v u∧¬Href v u):=by
      ext v
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
      have :=href v u
      tauto
    rw [he]
    exact (hquant.2.2 u).trans (le_max_right _ _)
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
