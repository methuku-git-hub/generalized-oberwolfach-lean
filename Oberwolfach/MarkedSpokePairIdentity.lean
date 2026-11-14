module

public import Oberwolfach.MarkedWheelRawCoordinates
public import Oberwolfach.MarkedRootOrder

@[expose] public section

/-! Exact resource identity of a spoke-wheel pair. It keeps both old hubs
and the marked incoming attachment; only the shared rim path cancels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ Hₖ:V→U→Prop}

 theorem markedRootOrder_eq_canonical (m:ℕ) (j:Bool):
    markedRootOrder m j=canonicalMarkedRotation (if j then Fin.last m else 2):=by
  apply Equiv.ext
  intro i
  cases j
  · change i+3=i+finRotate (m+1) (2:Fin (m+1))
    rw [finRotate_apply]
    congr 1
    apply Fin.ext
    change 3%(m+1)=(2%(m+1)+1%(m+1))%(m+1)
    rw [← Nat.add_mod]
  · simp only [markedRootOrder,ite_true,Equiv.refl_apply,canonicalMarkedRotation,finRotate_last,finCycle_apply,add_zero]

 theorem sum_initial_and_last {n:ℕ} (f:Fin (n+2)→ℤ)
    (h:∀ i:Fin n,f i.succ.castSucc=0):
    (∑ i,f i)=f 0+f (Fin.last (n+1)):=by
  rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  have hh:∀ i:Fin n,f i.castSucc.succ=0:=h
  simp only [hh,Finset.sum_const_zero,zero_add]
  have hlast:(Fin.last n).succ=Fin.last (n+1):=by apply Fin.ext;rfl
  rw [hlast]

 theorem raw_one_root_rim_difference (n:ℕ) (hn:2≤n) (p:Fin (n+1)→V)
    (v v':V) (j:Bool) (e:Finset V⊕(V×U)):
    (∑ i:Fin (n+2),physicalIntDelta
      (markedRawRimResource π (Fin.cons v p) (if j then Fin.last (n+1) else 2) i)
      (markedRawRimResource π (Fin.cons v' p) (if j then Fin.last (n+1) else 2) i) e)=
    physicalIntDelta (Sum.inl {v,p 0}) (Sum.inl {v',p 0}) e+
    physicalIntDelta (Sum.inl (if j then {p (Fin.last n),π v} else {p (Fin.last n),v}))
      (Sum.inl (if j then {p (Fin.last n),π v'} else {p (Fin.last n),v'})) e:=by
  have h2:((2:Fin (n+2)):ℕ)=2:=by change 2%(n+2)=2;exact Nat.mod_eq_of_lt (by omega)
  have hzero:(0:Fin (n+2))≠(if j then Fin.last (n+1) else 2):=by
    cases j <;> intro he <;> have hh:=congrArg Fin.val he
    · simp only [Bool.false_eq_true,ite_false,Fin.val_zero,h2] at hh;omega
    · simp only [ite_true,Fin.val_zero,Fin.val_last] at hh;omega
  have hlast:(Fin.last (n+1):Fin (n+2))≠2:=by
    intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_last,h2] at hh;omega
  have hmiddle:∀ i:Fin n,physicalIntDelta
      (markedRawRimResource π (Fin.cons v p) (if j then Fin.last (n+1) else 2) i.succ.castSucc)
      (markedRawRimResource π (Fin.cons v' p) (if j then Fin.last (n+1) else 2) i.succ.castSucc) e=0:=by
    intro i
    have hr:finRotate (n+2) i.succ.castSucc=i.succ.succ:=finRotate_castSucc_eq_succ (n+1) i.succ
    have hc:i.succ.castSucc=i.castSucc.succ:=rfl
    simp only [markedRawRimResource]
    rw [hr]
    simp only [hc,Fin.cons_succ,physicalIntDelta,sub_self]
  rw [sum_initial_and_last _ hmiddle]
  have hr0:finRotate (n+2) (0:Fin (n+2))=(0:Fin (n+1)).succ:=finRotate_castSucc_eq_succ (n+1) 0
  have hrzero (x:V):markedRawRimResource (U:=U) π (Fin.cons x p)
      (if j then Fin.last (n+1) else 2) 0=Sum.inl {x,p 0}:=by
    rw [markedRawRimResource,ite_eq_right hzero,hr0]
    rfl
  rw [hrzero,hrzero]
  have hrend (x:V):markedRawRimResource (U:=U) π (Fin.cons x p)
      (if j then Fin.last (n+1) else 2) (Fin.last (n+1))=
      Sum.inl (if j then {p (Fin.last n),π x} else {p (Fin.last n),x}):=by
    have he:(Fin.last (n+1):Fin (n+2))=(Fin.last n).succ:=by apply Fin.ext;rfl
    rw [markedRawRimResource,finRotate_last]
    cases j
    · rw [ite_eq_right (by simpa only [Bool.false_eq_true,ite_false] using hlast)]
      simp only [Bool.false_eq_true,ite_false,he,Fin.cons_succ,Fin.cons_zero]
    · simp only [ite_true,he,Fin.cons_succ,Fin.cons_zero]
  rw [hrend,hrend]

 theorem marked_spoke_pair_integer_identity (n:ℕ) (hn:2≤n)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:Fin (n+1)→V) (v v':V) (u u':U) (j:Bool)
    (A D:MarkedWheel tail head ktail khead (n+1) π b H₀ Hₖ)
    (hA:∀ i,A.1.val i=rootedCycleOrder (markedRootOrder (n+1) j) v p i)
    (hD:∀ i,D.1.val i=rootedCycleOrder (markedRootOrder (n+1) j) v' p i)
    (hAu:A.2.val=u) (hDu:D.2.val=u') (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources A then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources D then 1 else 0)=
    physicalIntDelta (Sum.inl {v,p 0}) (Sum.inl {v',p 0}) e+
    physicalIntDelta (Sum.inl (if j then {p (Fin.last n),π v} else {p (Fin.last n),v}))
      (Sum.inl (if j then {p (Fin.last n),π v'} else {p (Fin.last n),v'})) e+
    physicalIntDelta (Sum.inr (v,u)) (Sum.inr (v',u')) e+
    ∑ i,physicalIntDelta (Sum.inr (p i,u)) (Sum.inr (p i,u')) e:=by
  have ha:∀ i,A.1.val i=Fin.cons (α:=fun _=>V) v p
      (canonicalMarkedRotation (if j then Fin.last (n+1) else 2) i):=by
    intro i;rw [hA,markedRootOrder_eq_canonical];rfl
  have hd:∀ i,D.1.val i=Fin.cons (α:=fun _=>V) v' p
      (canonicalMarkedRotation (if j then Fin.last (n+1) else 2) i):=by
    intro i;rw [hD,markedRootOrder_eq_canonical];rfl
  rw [marked_wheel_raw_integer_difference hp A D _ _ _ ha hd,
    raw_one_root_rim_difference n hn p v v' j e,hAu,hDu,Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

end Oberwolfach
