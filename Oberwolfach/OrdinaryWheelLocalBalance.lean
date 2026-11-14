module

public import Oberwolfach.MarkedMixedOutsideBalance
public import Oberwolfach.OrdinaryWheelHubDiscrepancy
public import Oberwolfach.MarkedWheelFiniteBalance

@[expose] public section
/-! An ordinary wheel supplies the local balance equations in the typed
ambient graph when its spokes are unmarked.  Its hub equation is deliberately
left to the aggregate mixed accounting. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def ordinaryWheelTypedArcs {π:Equiv.Perm V} {b r:ℕ}
    (W:OrderedOrdinaryWheel (U:=U) π b r):Finset ((V×V)⊕(V×V)) :=
  Finset.univ.image (fun i:Fin r=>Sum.inl (W.1.val i,W.1.val (cycleNext i)))

theorem ordinary_wheel_unmarked_local_balance {π:Equiv.Perm V} {b r:ℕ}
    (HK:V→U→Prop) (W:OrderedOrdinaryWheel (U:=U) π b r)
    (hHK:∀i,¬HK (W.1.val i) W.2):
    MarkedFiniteLocalBalance (tail:=Prod.fst) (head:=Prod.snd) (ktail:=Prod.fst) (khead:=Prod.snd) (HK:=HK)
      (ordinaryWheelTypedArcs W) (ordinaryWheelSpokePairs W) := by
  let C:=W.1.val
  let f:=fun i:Fin r=>(Sum.inl (C i,C (cycleNext i)):((V×V)⊕(V×V)))
  let g:=fun i:Fin r=>(C i,W.2)
  have hC:Function.Injective C:=permutationSeparated_injective π b W.1.val W.1.property
  have hf:Function.Injective f:=by
    intro i j h
    apply hC
    exact congrArg Prod.fst (Sum.inl.inj h)
  have hg:Function.Injective g:=by
    intro i j h
    exact hC (congrArg Prod.fst h)
  have ha (p:((V×V)⊕(V×V))→Prop) [DecidablePred p]:
      ((ordinaryWheelTypedArcs W).filter p).card=(Finset.univ.filter (fun i=>p (f i))).card:=
    finite_injective_image_filter_card f hf p
  have hs (p:V×U→Prop) [DecidablePred p]:
      ((ordinaryWheelSpokePairs W).filter p).card=(Finset.univ.filter (fun i=>p (g i))).card:=
    finite_injective_image_filter_card g hg p
  have hnext (i:Fin r):cycleNext i=finRotate r i:=by
    cases r with
    | zero => exact Fin.elim0 i
    | succ n =>
      apply Fin.ext
      rw [cycleNext_val,coe_finRotate]
      by_cases hi:i=Fin.last n
      · subst i
        simp
      · have hv:i.val<n:=Fin.val_lt_last hi
        simp [hi,show i.val+1<n+1 by omega]
  have hrot (v:V):(Finset.univ.filter (fun i:Fin r=>C (cycleNext i)=v)).card=
      (Finset.univ.filter (fun i:Fin r=>C i=v)).card:=by
    simp_rw [hnext]
    convert filter_card_reindex_equiv (finRotate r) (fun i=>C i=v) using 1 <;> congr!
  constructor
  · intro v
    rw [ha,ha]
    convert hrot v using 1 <;> congr 1 <;> ext i <;> simp [f,g]
  · intro v
    rw [ha,hs]
    convert hrot v using 1 <;> congr 1 <;> ext i <;> simp [f,g]
  · intro v
    rw [ha,hs]
    simp only [f,g,Sum.elim_inl,Prod.fst,Prod.snd,markedArcType,Bool.false_eq_true, false_and,
      Finset.filter_false,Finset.card_empty]
    have hempty:(Finset.univ.filter (fun i:Fin r=>C i=v∧HK (C i) W.2))=∅:=by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hi
        exact False.elim (hHK i hi.2)
      · intro hi
        simp at hi
    rw [hempty]
    simp
end Oberwolfach
