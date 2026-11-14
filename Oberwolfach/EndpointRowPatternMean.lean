module

public import Oberwolfach.EndpointRowResources
public import Oberwolfach.EndpointParentMatching

@[expose] public section

/-! The endpoint pattern target is the unchanged eligible parent row mass.
The hub multiplicity and original denominator are cancelled explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpointRowCandidates_sum (E:SimpleGraph V) (A:Finset V) (B:Finset U) (v:V)
    (hE:∀ w,E.Adj v w→w∈A) (w:V→ℝ):
    (∑ p:EndpointRowCandidates E A B v,w p.val.2)=
      (B.card:ℝ)*∑ z,if E.Adj v z then w z else 0:=by
  have hs:(∑ p:U×V,if p.1∈B∧p.2∈A∧E.Adj v p.2 then w p.2 else 0)=
      ∑ p:EndpointRowCandidates E A B v,w p.val.2:=by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  rw [←hs,Fintype.sum_prod_type]
  have hz (z:V):(z∈A∧E.Adj v z)↔E.Adj v z:=⟨And.right,fun h=>⟨hE z h,h⟩⟩
  have hinner (u:U):(∑ z,if u∈B∧z∈A∧E.Adj v z then w z else 0)=
      if u∈B then ∑ z,if E.Adj v z then w z else 0 else 0:=by
    by_cases hu:u∈B <;> simp only [hu,true_and,false_and,ite_true,ite_false,Finset.sum_const_zero,hz]
  simp_rw [hinner]
  rw [←Finset.sum_filter]
  have he:Finset.univ.filter (fun u:U=>u∈B)=B:=by ext u;simp
  rw [he]
  simp

theorem endpoint_row_pattern_mean (P F:SimpleGraph V) (A:Finset V) (B:Finset U) (x v:V)
    (hv:v∈A∩P.neighborFinset x) (hFx:¬F.Adj x v)
    (weight:Sym2 V→ℝ) (hzero:∀ u∈A∩P.neighborFinset x,¬P.Adj v u→weight s(v,u)=0)
    (pR pH:ℝ) (hpR:0<pR) (hpH:0<pH) (hB:0<B.card):
    pR^2*pH^3*(∑ p:EndpointRowCandidates (endpointEligibleGraph P F (A∩P.neighborFinset x) x) A B v,
      weight s(v,p.val.2)/(B.card*pR^2*pH^3))=
      endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w)):=by
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  have hE (w:V) (h:E.Adj v w):w∈A:=(Finset.mem_inter.mp h.2.1).1
  rw [endpointRowCandidates_sum E A B v hE (fun w=>weight s(v,w)/(B.card*pR^2*pH^3))]
  have hsum:(∑ w,if E.Adj v w then weight s(v,w)/(B.card*pR^2*pH^3) else 0)=
      (∑ w,if E.Adj v w then weight s(v,w) else 0)/(B.card*pR^2*pH^3):=by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  rw [hsum]
  have he:=endpoint_row_target_as_edges P F (A∩P.neighborFinset x) x v hv hFx weight hzero
  rw [←graph_weighted_incidence_sum] at he
  rw [he]
  have hb:(0:ℝ)<B.card:=Nat.cast_pos.mpr hB
  change pR^2*pH^3*((B.card:ℝ)*(_/(B.card*pR^2*pH^3)))=_
  field_simp
  rfl

end Oberwolfach
