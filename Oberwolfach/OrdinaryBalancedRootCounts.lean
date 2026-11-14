module

public import Oberwolfach.OrdinaryTransformerSpokeSets
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! The size bound for the realised transformer depends on the number
of active old hubs and their degrees, never on forbidden labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem balanced_root_edge_counts (G:SimpleGraph V) (H₀:V→U→Prop)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (q nU:ℕ) (hq:∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤q)
    (hnU:Fintype.card {u:U // ∃ v,H₀ v u}≤nU):
    G.edgeFinset.card=Fintype.card {e:V×U // H₀ e.1 e.2}∧
    Fintype.card (Σ v,G.neighborSet v)=2*G.edgeFinset.card∧
    G.edgeFinset.card≤nU*q:=by
  let J:={e:V×U // H₀ e.1 e.2}
  let e:J≃(Σ v,{u:U // H₀ v u}):={
    toFun:=fun j=>⟨j.val.1,⟨j.val.2,j.property⟩⟩
    invFun:=fun j=>⟨(j.1,j.2.val),j.2.property⟩
    left_inv:=by rintro ⟨⟨v,u⟩,h⟩;rfl
    right_inv:=by rintro ⟨v,u⟩;rfl}
  have hc:Fintype.card J=∑ v,((Finset.univ:Finset U).filter (H₀ v)).card:=by
    rw [Fintype.card_congr e,Fintype.card_sigma]
    simp only [Fintype.card_subtype]
  have hb:G.edgeFinset.card=Fintype.card J:=by
    have hh:=G.sum_degrees_eq_twice_card_edges
    simp_rw [hbalance] at hh
    rw [←Finset.mul_sum,←hc] at hh
    omega
  have hi:Fintype.card (Σ v,G.neighborSet v)=2*G.edgeFinset.card:=by
    rw [Fintype.card_sigma]
    simp_rw [Set.fintypeCard_eq_ncard,SimpleGraph.ncard_neighborSet]
    exact G.sum_degrees_eq_twice_card_edges
  let I:={u:U // ∃ v,H₀ v u}
  let e':J≃(Σ u:I,{v:V // H₀ v u.val}):={
    toFun:=fun j=>⟨⟨j.val.2,⟨j.val.1,j.property⟩⟩,⟨j.val.1,j.property⟩⟩
    invFun:=fun j=>⟨(j.2.val,j.1.val),j.2.property⟩
    left_inv:=by rintro ⟨⟨v,u⟩,h⟩;rfl
    right_inv:=by rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩;rfl}
  refine ⟨hb,hi,?_⟩
  rw [hb,Fintype.card_congr e',Fintype.card_sigma]
  calc
    _≤∑ _u:I,q:=Finset.sum_le_sum (fun u _=>by simpa only [Fintype.card_subtype] using hq u.val)
    _=Fintype.card I*q:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
    _≤nU*q:=Nat.mul_le_mul_right _ hnU

end Oberwolfach
