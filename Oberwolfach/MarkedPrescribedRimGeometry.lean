module

public import Oberwolfach.MarkedPrescribedRimExtension

@[expose] public section

/-! The actual prescribed physical edge and auxiliary endpoint isolation
for a two-root marked wheel. Global physical injectivity is used exactly
when recovering an old typed arc from a common physical edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b n m:ℕ}

theorem marked_two_root_rows (p:Fin (n+1)→V) (v w:V) (ρ:Equiv.Perm (Fin (n+3)))
    (C:MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hC:∀ a,C.1.val a=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (ρ a)):
    markedWheelRows C=insert v (insert w (Finset.univ.image p)):=by
  ext x
  simp only [markedWheelRows,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨a,ha⟩
    rw [hC] at ha
    generalize ρ a=i at ha
    revert ha
    refine Fin.cases ?_ (fun i=>?_) i
    · intro ha;exact Or.inl ha.symm
    · refine Fin.cases ?_ (fun i=>?_) i
      · intro ha;exact Or.inr (Or.inl ha.symm)
      · intro ha;exact Or.inr (Or.inr ⟨i,ha⟩)
  · rintro (rfl|rfl|⟨i,hi⟩)
    · exact ⟨ρ.symm 0,by rw [hC,Equiv.apply_symm_apply];rfl⟩
    · exact ⟨ρ.symm (0:Fin (n+2)).succ,by rw [hC,Equiv.apply_symm_apply];rfl⟩
    · exact ⟨ρ.symm i.succ.succ,by rw [hC,Equiv.apply_symm_apply];exact hi⟩

theorem marked_two_root_contains_arc (hn:2≤n) (p:Fin (n+1)→V) (v w:V) (j:Bool)
    (C:MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hC:∀ a,C.1.val a=Fin.cons (α:=fun _=>V) v (Fin.cons w p)
      (canonicalMarkedRotation (if j then 0 else 3) a)):
    Sum.inl (if j then ({v,π w}:Finset V) else {v,w})∈markedWheelPhysicalResources C:=by
  let k:Fin (n+3):=if j then 0 else 3
  have he:=marked_wheel_raw_rim_position C (Fin.cons v (Fin.cons w p)) k hC 0
  have hr0:finRotate (n+3) (0:Fin (n+3))=(0:Fin (n+2)).succ:=finRotate_castSucc_eq_succ (n+2) 0
  have h03:(0:Fin (n+3))≠3:=by
    intro h;have hh:=congrArg Fin.val h
    change 0=3%(n+3) at hh
    rw [Nat.mod_eq_of_lt (by omega)] at hh;omega
  have he':markedWheelPositionResource C (Sum.inl ((canonicalMarkedRotation k).symm 0))=
      Sum.inl (if j then ({v,π w}:Finset V) else {v,w}):=by
    rw [he]
    cases j <;> simp only [markedRawRimResource,k,Bool.false_eq_true,ite_false,ite_true,
      h03,hr0,Fin.cons_zero,Fin.cons_succ]
  rw [←he',←markedWheelPositionResource_image]
  exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

theorem marked_arc_witness (j:Bool) (v w:V) (hroot:markedArcPresent tail head ktail khead j v w):
    ∃ e:E⊕K,Sum.elim tail ktail e=v∧Sum.elim head khead e=w∧
      markedPhysicalEdge tail head ktail khead π e=(if j then {v,π w} else {v,w}):=by
  cases j
  · obtain ⟨e,ht,hh⟩:=hroot
    exact ⟨Sum.inl e,ht,hh,by simp only [markedPhysicalEdge,Sum.elim_inl,ht,hh,Bool.false_eq_true,ite_false]⟩
  · obtain ⟨e,ht,hh⟩:=hroot
    exact ⟨Sum.inr e,ht,hh,by simp only [markedPhysicalEdge,Sum.elim_inr,ht,hh,ite_true]⟩

theorem marked_prescribed_arc_avoids_family
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (R:Finset V) (old:I→Finset V)
    (hold:∀ i a,(C i).1.val a∈R→(C i).1.val (finRotate (m+1) a)∈R→
      markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b (C i).1 a)=old i)
    (j:Bool) (v w:V) (hv:v∈R) (hw:w∈R)
    (hroot:markedArcPresent tail head ktail khead j v w)
    (hne:∀ i,old i≠(if j then {v,π w} else {v,w})):
    ¬(markedFamilyRim C).Adj v (if j then π w else w):=by
  intro hadj
  obtain ⟨i,_,he⟩:=SimpleGraph.iSup_adj.mp hadj
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he
  obtain ⟨e,ht,hh,hphys⟩:=marked_arc_witness (π:=π) j v w hroot
  have hpair:({v,if j then π w else w}:Finset V)=(if j then {v,π w} else {v,w}):=by cases j <;> rfl
  have heq:=hp (ha.trans (hpair.trans hphys.symm))
  have hc:=markedCycleTypedEdge_endpoints tail head ktail khead m π b (C i).1 a
  have htv:(C i).1.val a=v:=hc.1.symm.trans ((congrArg (Sum.elim tail ktail) heq).trans ht)
  have hhw:(C i).1.val (finRotate (m+1) a)=w:=hc.2.symm.trans ((congrArg (Sum.elim head khead) heq).trans hh)
  exact hne i ((hold i a (htv ▸ hv) (hhw ▸ hw)).symm.trans (ha.trans hpair))

end Oberwolfach
