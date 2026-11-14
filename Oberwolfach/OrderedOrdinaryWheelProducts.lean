module

public import Oberwolfach.OrderedOrdinaryWheelGeometry

@[expose] public section
/-! All r physical edges and r spokes of an ordered ordinary wheel are distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinaryResources_constant_product (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r) (p s:ℝ):
    (∏ a∈orderedOrdinaryResources W,Sum.elim (fun _=>p) (fun _=>s) a)=p^r*s^r:=by
  have hd:Disjoint (Finset.univ.image (fun i:Fin r=>(Sum.inl (W.1.val i,W.1.val (cycleNext i)):(V×V)⊕(V×U))))
      (Finset.univ.image (fun i:Fin r=>Sum.inr (W.1.val i,W.2))) :=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨b,_,hh⟩:=Finset.mem_image.mp hf
    cases hh
  have hrim:Function.Injective (fun i:Fin r=>(Sum.inl (W.1.val i,W.1.val (cycleNext i)):(V×V)⊕(V×U))):=by
    intro i j hij
    have hh:=congrArg (fun e:V×V=>s(e.1,e.2)) (Sum.inl.inj hij)
    exact orderedOrdinaryPhysical_edge_injective hr W hh
  have hspoke:Function.Injective (fun i:Fin r=>(Sum.inr (W.1.val i,W.2):(V×V)⊕(V×U))):=by
    intro i j hij
    exact permutationSeparated_injective π b W.1.val W.1.property (congrArg Prod.fst (Sum.inr.inj hij))
  unfold orderedOrdinaryResources
  rw [Finset.prod_union hd,Finset.prod_image (fun a _ b _ h=>hrim h),Finset.prod_image (fun a _ b _ h=>hspoke h)]
  simp

theorem orderedOrdinary_rim_omitted_product (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r) (p s:ℝ) (hp:p≠0)
    (e:V×V) (he:Sum.inl e∈orderedOrdinaryResources W):
    (∏ a∈orderedOrdinaryResources W\{Sum.inl e},Sum.elim (fun _=>p) (fun _=>s) a)=p^(r-1)*s^r:=by
  have hh:=Finset.mul_prod_erase (orderedOrdinaryResources W) (Sum.elim (fun _=>p) (fun _=>s)) he
  have heq:(orderedOrdinaryResources W).erase (Sum.inl e)=orderedOrdinaryResources W\{Sum.inl e}:=by ext a;simp [and_comm]
  rw [heq,orderedOrdinaryResources_constant_product W hr] at hh
  apply mul_left_cancel₀ hp
  calc
    _ = p^r*s^r := hh
    _ = (p*p^(r-1))*s^r := by rw [←pow_succ',Nat.sub_add_cancel (by omega:1≤r)]
    _ = _ := by ring

theorem orderedOrdinary_spoke_omitted_product (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r) (p s:ℝ) (hs:s≠0)
    (a:V×U) (ha:Sum.inr a∈orderedOrdinaryResources W):
    (∏ e∈orderedOrdinaryResources W\{Sum.inr a},Sum.elim (fun _=>p) (fun _=>s) e)=p^r*s^(r-1):=by
  have hh:=Finset.mul_prod_erase (orderedOrdinaryResources W) (Sum.elim (fun _=>p) (fun _=>s)) ha
  have heq:(orderedOrdinaryResources W).erase (Sum.inr a)=orderedOrdinaryResources W\{Sum.inr a}:=by ext e;simp [and_comm]
  rw [heq,orderedOrdinaryResources_constant_product W hr] at hh
  apply mul_left_cancel₀ hs
  calc
    _ = p^r*s^r := hh
    _ = p^r*(s*s^(r-1)) := by rw [←pow_succ',Nat.sub_add_cancel (by omega:1≤r)]
    _ = _ := by ring
end Oberwolfach
