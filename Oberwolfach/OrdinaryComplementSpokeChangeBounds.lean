module

public import Oberwolfach.OrdinaryRimEditDegreeComparison
public import Oberwolfach.OrdinaryReservedSpokeChangeBounds
public import Oberwolfach.OrdinaryComplementRemainderBalance
public import Oberwolfach.OrdinaryReservedSpokeCardinality

@[expose] public section
/-! The actual complementary factor embedding inherits reference-spoke
    closeness from its rim-edit bound and sampled reference degree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_reference_spoke_change_bounds {n q r:ℕ}
    (Target Reference:SimpleGraph (Fin n)) (hTarget:Target.IsRegularOfDegree (2*q))
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→Target.Adj (f u x) (f u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (f u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (f v)))
    (Href:Fin n→Fin q→Prop) (rsv b e t:ℝ)
    (hAvoid:∀u x,¬Href (f u x) u)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor
      ((Target\ordinaryEmbeddedComplements Fs C f).Adj v w) (Reference.Adj v w))).card:ℝ)≤b)
    (hRefBalance:∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)
    (hRefColumns:∀u,|((Finset.univ.filter (fun v=>Href v u)).card:ℝ)-rsv*n|≤t):
    let H:=fun v u=>v∉Set.range (f u);
    (∀v,2*((Finset.univ.filter (fun u=>H v u ∧ ¬Href v u)).card:ℝ)≤b+e) ∧
    (∀u,((Finset.univ.filter (fun v=>H v u ∧ ¬Href v u)).card:ℝ)≤t):=by
  intro H
  let Q:=Target\ordinaryEmbeddedComplements Fs C f
  letI:DecidableRel Q.Adj:=Classical.decRel _
  letI:∀v,DecidablePred (H v):=fun v u=>Classical.propDecidable (H v u)
  letI:∀u,DecidablePred (fun v=>H v u):=fun u v=>Classical.propDecidable (H v u)
  obtain ⟨hb,hd⟩:=ordinary_complement_remainder_balance Target hTarget Fs hFs C hsize f hC hCC
  have hbal:∀v,(Q.degree v:ℝ)=2*((Finset.univ.filter (H v)).card:ℝ):=by
    intro v
    have hh:=hb v
    have hh':Q.degree v=2*(Finset.univ.filter (H v)).card:=by
      convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
    exact_mod_cast hh'
  have hsub:∀v u,Href v u→H v u:=by
    intro v u hv ⟨x,hx⟩
    exact hAvoid u x (hx ▸ hv)
  have hEditQ:∀v,((Finset.univ.filter (fun w=>Xor (Q.Adj v w) (Reference.Adj v w))).card:ℝ)≤b:=by
    intro v
    convert hEdit v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  have hRim:=ordinary_rim_degree_le_reference_add_edits Q Reference b hEditQ
  have hRow:∀v,(Reference.degree v:ℝ)≤2*((Finset.univ.filter (Href v)).card:ℝ)+e:=by
    intro v
    have hh:=(abs_le.mp (hRefBalance v)).2
    linarith
  have hUpper:∀u,((Finset.univ.filter (fun v=>H v u)).card:ℝ)≤rsv*n:=by
    intro u
    have hh:=(ordinary_reserved_spoke_cardinality (Fs u) (C u) (hsize u) (f u) (fun v=>H v u) (fun _=>Iff.rfl)).1
    have hhNat:(Finset.univ.filter (fun v=>H v u)).card=r*(C u).card:=by
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    have hh':((Finset.univ.filter (fun v=>H v u)).card:ℝ)=(r:ℝ)*(C u).card:=by exact_mod_cast hhNat
    exact le_of_eq (hh'.trans (hCard u))
  have hLower:∀u,rsv*n-t≤((Finset.univ.filter (fun v=>Href v u)).card:ℝ):=by
    intro u
    have hh:=(abs_le.mp (hRefColumns u)).1
    linarith
  have hbalClassical:∀v,(Q.degree v:ℝ)=2*((Finset.univ.filter (H v)).card:ℝ):=by
    intro v
    convert hbal v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  convert ordinary_reserved_spoke_change_bounds Q Reference H Href b e (fun _=>rsv*n) (fun _=>t)
    hsub hbalClassical hRim hRow hUpper hLower using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
