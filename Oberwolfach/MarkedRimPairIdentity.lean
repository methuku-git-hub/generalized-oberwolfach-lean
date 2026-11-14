module

public import Oberwolfach.MarkedWheelRawCoordinates

@[expose] public section

/-! Exact integer identity for an actual rim-wheel pair. The shared path
cancels; the old arc, two attachments and two root spokes remain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ Hₖ:V→U→Prop}

 theorem sum_two_initial_and_last {n:ℕ} (f:Fin (n+3)→ℤ)
    (h:∀ i:Fin n,f i.succ.succ.castSucc=0):
    (∑ i,f i)=f 0+f (0:Fin (n+2)).succ+f (Fin.last (n+2)):=by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  have hh:∀ i:Fin n,f i.castSucc.succ.succ=0:=h
  simp only [hh,Finset.sum_const_zero,zero_add]
  have hlast:(Fin.last n).succ.succ=Fin.last (n+2):=by apply Fin.ext;rfl
  rw [hlast]
  ring

 theorem raw_two_root_rim_difference (n:ℕ) (hn:2≤n) (p:Fin (n+1)→V)
    (v w v' w':V) (j:Bool) (e:Finset V⊕(V×U)):
    (∑ i:Fin (n+3),physicalIntDelta
      (markedRawRimResource π (Fin.cons v (Fin.cons w p)) (if j then 0 else 3) i)
      (markedRawRimResource π (Fin.cons v' (Fin.cons w' p)) (if j then 0 else 3) i) e)=
    physicalIntDelta (Sum.inl (if j then {v,π w} else {v,w}))
      (Sum.inl (if j then {v',π w'} else {v',w'})) e+
    physicalIntDelta (Sum.inl {w,p 0}) (Sum.inl {w',p 0}) e+
    physicalIntDelta (Sum.inl {p (Fin.last n),v}) (Sum.inl {p (Fin.last n),v'}) e:=by
  have h3:((3:Fin (n+3)):ℕ)=3:=by change 3%(n+3)=3;exact Nat.mod_eq_of_lt (by omega)
  have hzero:(0:Fin (n+3))≠3:=by intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_zero,h3] at hh;omega
  have hone:(0:Fin (n+2)).succ≠(if j then (0:Fin (n+3)) else 3):=by
    cases j
    · intro he;have hh:=congrArg Fin.val he;simp only [Bool.false_eq_true,ite_false,Fin.val_succ,Fin.val_zero,h3] at hh;omega
    · exact Fin.succ_ne_zero _
  have hlast:(Fin.last (n+2):Fin (n+3))≠(if j then 0 else 3):=by
    cases j
    · intro he;have hh:=congrArg Fin.val he;simp only [Bool.false_eq_true,ite_false,Fin.val_last,h3] at hh;omega
    · intro he;have hh:=congrArg Fin.val he;simp only [ite_true,Fin.val_last,Fin.val_zero] at hh;omega
  have hmiddle:∀ i:Fin n,physicalIntDelta
      (markedRawRimResource π (Fin.cons v (Fin.cons w p)) (if j then 0 else 3) i.succ.succ.castSucc)
      (markedRawRimResource π (Fin.cons v' (Fin.cons w' p)) (if j then 0 else 3) i.succ.succ.castSucc) e=0:=by
    intro i
    have hc:i.succ.succ.castSucc=i.castSucc.succ.succ:=rfl
    have hr:finRotate (n+3) i.succ.succ.castSucc=i.succ.succ.succ:=finRotate_castSucc_eq_succ (n+2) i.succ.succ
    simp only [markedRawRimResource]
    rw [hr]
    simp only [hc,Fin.cons_succ,physicalIntDelta,sub_self]
  rw [sum_two_initial_and_last _ hmiddle]
  have hr0:finRotate (n+3) (0:Fin (n+3))=(0:Fin (n+2)).succ:=finRotate_castSucc_eq_succ (n+2) 0
  have hr1:finRotate (n+3) (0:Fin (n+2)).succ=(0:Fin (n+1)).succ.succ:=by
    change finRotate (n+3) ((0:Fin (n+1)).succ.castSucc)=(0:Fin (n+1)).succ.succ
    exact finRotate_castSucc_eq_succ _ _
  have hlastpos:(Fin.last (n+2):Fin (n+3))=(Fin.last n).succ.succ:=rfl
  have hrlast (x y:V):markedRawRimResource (U:=U) π (Fin.cons x (Fin.cons y p))
      (if j then 0 else 3) (Fin.last (n+2))=Sum.inl {p (Fin.last n),x}:=by
    rw [markedRawRimResource,ite_eq_right hlast,finRotate_last]
    simp only [hlastpos,Fin.cons_succ,Fin.cons_zero]
  rw [hrlast,hrlast]
  simp only [markedRawRimResource,hone,ite_false,hr0,hr1,Fin.cons_succ,Fin.cons_zero]
  cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true,hzero]

 theorem marked_rim_pair_integer_identity (n:ℕ) (hn:2≤n)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:Fin (n+1)→V) (v w v' w':V) (u:U) (j:Bool)
    (A D:MarkedWheel tail head ktail khead (n+2) π b H₀ Hₖ)
    (hA:∀ i,A.1.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i))
    (hD:∀ i,D.1.val i=Fin.cons (α:=fun _=>V) v' (Fin.cons w' p) (canonicalMarkedRotation (if j then 0 else 3) i))
    (hAu:A.2.val=u) (hDu:D.2.val=u) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources A then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources D then 1 else 0)=
    physicalIntDelta (Sum.inl (if j then {v,π w} else {v,w}))
      (Sum.inl (if j then {v',π w'} else {v',w'})) e+
    physicalIntDelta (Sum.inl {w,p 0}) (Sum.inl {w',p 0}) e+
    physicalIntDelta (Sum.inl {p (Fin.last n),v}) (Sum.inl {p (Fin.last n),v'}) e+
    physicalIntDelta (Sum.inr (v,u)) (Sum.inr (v',u)) e+
    physicalIntDelta (Sum.inr (w,u)) (Sum.inr (w',u)) e:=by
  rw [marked_wheel_raw_integer_difference hp A D _ _ _ hA hD,
    raw_two_root_rim_difference n hn p v w v' w' j e,hAu,hDu]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,physicalIntDelta,sub_self,Finset.sum_const_zero,add_zero]
  ring

end Oberwolfach
