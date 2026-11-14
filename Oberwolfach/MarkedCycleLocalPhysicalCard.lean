module

public import Oberwolfach.WheelRunPhysicalEdgeSaturation
public import Oberwolfach.RawMarkedCandidateGeometry

@[expose] public section
/-! The edges within one separated marked wheel are distinct even when the
ambient map from typed arcs to physical edges is not globally injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_cycle_local_physical_edges_card
    {V E L:Type} [Fintype V] [LinearOrder V]
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V)
    (hm:2≤m) (hb:1≤b) (C:MarkedCycleTuple tail head ktail khead m π b):
    (markedCyclePhysicalEdges tail head ktail khead m π b C).card=m+1:=by
  have hinj:=separated_successor_edges_injective hm π b hb C.val C.property.1
  have heq:∀i:Fin m,markedPhysicalEdge tail head ktail khead π
      (markedCycleTypedEdge tail head ktail khead m π b C i.castSucc)={C.val i.castSucc,C.val i.succ}:=by
    intro i
    simp only [markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,Sum.elim_inl]
    rw [(Classical.choose_spec (C.property.2.1 i)).1,(Classical.choose_spec (C.property.2.1 i)).2]
  have hlast:markedPhysicalEdge tail head ktail khead π
      (markedCycleTypedEdge tail head ktail khead m π b C (Fin.last m))={C.val (Fin.last m),π (C.val 0)}:=by
    simp only [markedCycleTypedEdge,Fin.snoc_last,markedPhysicalEdge,Sum.elim_inr]
    rw [(Classical.choose_spec C.property.2.2).1,(Classical.choose_spec C.property.2.2).2]
  have hlocal:Function.Injective (markedPhysicalEdge tail head ktail khead π ∘
      markedCycleTypedEdge tail head ktail khead m π b C):=by
    intro i j
    refine Fin.lastCases ?_ (fun i=>?_) i <;> refine Fin.lastCases ?_ (fun j=>?_) j
    · intro _;rfl
    · intro h
      simp only [Function.comp_apply,hlast,heq] at h
      have he:s(C.val (Fin.last m),π (C.val 0))=s(C.val j.castSucc,C.val j.succ):=by
        apply sym2_toFinset_injective_local
        simpa only [Sym2.toFinset_mk_eq] using h
      have hh:(Sum.inr ():Fin m⊕Unit)=Sum.inl j:=hinj he
      cases hh
    · intro h
      simp only [Function.comp_apply,hlast,heq] at h
      have he:s(C.val i.castSucc,C.val i.succ)=s(C.val (Fin.last m),π (C.val 0)):=by
        apply sym2_toFinset_injective_local
        simpa only [Sym2.toFinset_mk_eq] using h
      have hh:(Sum.inl i:Fin m⊕Unit)=Sum.inr ():=hinj he
      cases hh
    · intro h
      simp only [Function.comp_apply,heq] at h
      have he:s(C.val i.castSucc,C.val i.succ)=s(C.val j.castSucc,C.val j.succ):=by
        apply sym2_toFinset_injective_local
        simpa only [Sym2.toFinset_mk_eq] using h
      have hh:(Sum.inl i:Fin m⊕Unit)=Sum.inl j:=hinj he
      exact congrArg Fin.castSucc (Sum.inl.inj hh)
  rw [markedCyclePhysicalEdges,Finset.card_image_of_injective _ hlocal]
  simp
end Oberwolfach
