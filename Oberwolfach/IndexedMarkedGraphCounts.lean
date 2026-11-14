module

public import Oberwolfach.IndexedMarkedGraph

@[expose] public section

/-! Summing the exact local balance identities gives the four edge-type
counts used to choose the disjoint wheel endpoint of the absorber diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]

theorem sum_finite_fiber_card (f:A→V):
    (∑ v:V,Fintype.card {a:A // f a=v})=Fintype.card A:=by
  rw [←Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

theorem sum_finite_typed_fiber_card (f:A→V) (j:A→Bool) (t:Bool):
    (∑ v:V,Fintype.card {a:A // f a=v∧j a=t})=Fintype.card {a:A // j a=t}:=by
  rw [←Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun:=fun x=>⟨x.2.val,x.2.property.2⟩
    invFun:=fun a=>⟨f a.val,⟨a.val,rfl,a.property⟩⟩
    left_inv:=by rintro ⟨v,a,hv,hj⟩;subst v;rfl
    right_inv:=fun _=>rfl}

theorem bool_type_card_partition (j:A→Bool):
    Fintype.card {a:A // j a=false}+Fintype.card {a:A // j a=true}=Fintype.card A:=by
  have hh:=sum_finite_fiber_card j
  simpa only [Fintype.sum_bool,add_comm] using hh

theorem IndexedMarkedGraph.rim_spoke_card (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m):Fintype.card A=Fintype.card S:=by
  rw [←sum_finite_fiber_card G.dst,←sum_finite_fiber_card G.row]
  exact Finset.sum_congr rfl (fun v _=>hG.row v)

theorem IndexedMarkedGraph.marked_card (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m):
    Fintype.card {a:A // G.jr a=true}=Fintype.card {s:S // G.js s=true}:=by
  rw [←sum_finite_typed_fiber_card G.dst G.jr true,←sum_finite_typed_fiber_card G.row G.js true]
  exact Finset.sum_congr rfl (fun v _=>hG.marked v)

theorem IndexedMarkedGraph.ordinary_spoke_card (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m):
    Fintype.card {s:S // G.js s=false}=m*Fintype.card {s:S // G.js s=true}:=by
  rw [←sum_finite_typed_fiber_card G.hub G.js false,←sum_finite_typed_fiber_card G.hub G.js true,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun u _=>hG.hub u)

theorem IndexedMarkedGraph.ordinary_rim_card (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m):
    Fintype.card {a:A // G.jr a=false}=m*Fintype.card {s:S // G.js s=true}:=by
  have h₁:=G.rim_spoke_card m hG
  have h₂:=G.marked_card m hG
  have h₃:=G.ordinary_spoke_card m hG
  have h₄:=bool_type_card_partition G.jr
  have h₅:=bool_type_card_partition G.js
  omega

end Oberwolfach
