module

public import Oberwolfach.MarkedCrossFamilyPacking
public import Oberwolfach.MarkedAttachmentArcIsolation

@[expose] public section

/-! A vertex wheel meets an earlier rim or spoke wheel only at its fixed
attachments. The assigned hub inequalities then exclude shared spokes,
while the absence of an attachment-to-attachment arc excludes shared rims. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_vertex_cross_packing (n:ℕ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C D:MarkedWheel tail head ktail khead (n+3) π b H₀ HK)
    (R A:Finset V) (p:Fin (n+3)↪V) (v:V) (j:Bool)
    (hC:∀ i,C.1.val i∈R∪A) (hv:v∉R∪A)
    (hD:∀ i,D.1.val i=rootedCycleOrder (markedRootOrder (n+3) j) v p i)
    (hpR:∀ i,p i∉R)
    (hpA:∀ i,p i∈A→p i∈({p 0,p (Fin.last (n+2))}:Finset V))
    (hfirst:∀ i,C.1.val i=p 0→C.2.val≠D.2.val)
    (hlast:∀ i,C.1.val i=p (Fin.last (n+2))→C.2.val≠D.2.val):
    Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources D):=by
  have hval:∀ i,D.1.val i=v∨∃ z,D.1.val i=p z:=by
    intro i
    have hh:D.1.val i∈Finset.univ.image D.1.val:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [funext hD,rootedCycleOrder_vertices] at hh
    rw [←hD i] at hh
    rcases Finset.mem_insert.mp hh with hh|hh
    · exact Or.inl hh
    · obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hh
      exact Or.inr ⟨z,hz.symm⟩
  have hshared:∀ i k,C.1.val i=D.1.val k→D.1.val k∈A:=by
    intro i k he
    rcases hval k with hv'|⟨z,hz⟩
    · exact False.elim (hv ((he.trans hv') ▸ hC i))
    · have hc:=hC i
      rcases Finset.mem_union.mp hc with hc|hc
      · exact False.elim (hpR z ((he.trans hz) ▸ hc))
      · exact he ▸ hc
  apply marked_wheels_disjoint_of_shared_labels hp C D A hshared
    (marked_fixed_attachment_no_attachment_arc n p v j A
      (fun h=>hv (Finset.mem_union_right _ h)) hpA D hD) ?_
  intro i k he
  rcases hval k with hv'|⟨z,hz⟩
  · exact False.elim (hv ((he.trans hv') ▸ hC i))
  · have hzA:p z∈A:=hz ▸ hshared i k he
    rcases Finset.mem_insert.mp (hpA z hzA) with hh|hh
    · exact hfirst i (he.trans (hz.trans hh))
    · exact hlast i (he.trans (hz.trans (Finset.mem_singleton.mp hh)))

end Oberwolfach
