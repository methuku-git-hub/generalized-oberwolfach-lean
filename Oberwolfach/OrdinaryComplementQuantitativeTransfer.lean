module

public import Oberwolfach.OrdinaryComplementSpokeChangeBounds
public import Oberwolfach.OrdinaryRemainderReferenceEdits

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

theorem ordinary_complement_quantitative_reference_transfer {n q r:ℕ}
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
    (hAvoid:∀u x,¬Href (f u x) u)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hUncovered:∀v,(((Sample\Reference)\ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤κ)
    (hUsed:∀v,((Reference⊓ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤loss)
    (hRefBalance:∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)
    (hRefColumns:∀u,|((Finset.univ.filter (fun v=>Href v u)).card:ℝ)-rsv*n|≤t):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u);
    (∀v,((Finset.univ.filter (fun w=>Xor (Q.Adj v w) (Reference.Adj v w))).card:ℝ)≤b+κ+loss) ∧
    (∀v,2*((Finset.univ.filter (fun u=>H v u ∧ ¬Href v u)).card:ℝ)≤b+κ+loss+e) ∧
    (∀u,((Finset.univ.filter (fun v=>H v u ∧ ¬Href v u)).card:ℝ)≤t):=by
  intro Q H
  have hE:=ordinary_remainder_reference_edit_bound Target Sample Reference (ordinaryEmbeddedComplements Fs C f)
    hRef b κ loss hEdit hUncovered hUsed
  have hS:=ordinary_complement_reference_spoke_change_bounds Target Reference hTarget Fs hFs C hsize f hC hCC
    Href rsv (b+κ+loss) e t hAvoid hCard hE hRefBalance hRefColumns
  exact ⟨hE,hS⟩
end Oberwolfach
