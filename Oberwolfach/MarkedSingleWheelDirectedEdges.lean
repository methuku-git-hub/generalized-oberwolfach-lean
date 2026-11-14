module

public import Oberwolfach.MarkedWheelWalkPhysicalEdgeSet

@[expose] public section
/-! The physical marked-wheel rim walk follows the original directions of all
ordinary arcs and the physical image of its marked arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_single_wheel_directed_walk_with_edges
    {V E K:Type*} [DecidableEq V] (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (R:V→V→Prop) (hER:∀e:E,R (tail e) (head e))
    (hKR:∀e:K,R (ktail e) (π (khead e))):
    ∃p:G.Walk (C.val 0) (π (C.val 0)),p.IsPath ∧ p.length=m+1 ∧
      p.support.dropLast=List.ofFn C.val ∧
      walkPhysicalEdges p=markedCyclePhysicalEdges tail head ktail khead m π b C ∧
      ∀k,k<p.length→R (p.getVert k) (p.getVert (k+1)):=by
  obtain ⟨f,hprefix,hlast,p,hp,hlen,hsupp⟩:=marked_single_wheel_physical_walk G tail head ktail khead m b π hb C hroot hE hK
  have hdir:∀j:Fin (m+1),R (f j.castSucc) (f j.succ):=by
    intro j
    refine Fin.lastCases ?_ (fun i=>?_) j
    · obtain ⟨e,he₁,he₂⟩:=C.property.2.2
      have h:=hKR e
      rw [he₁,he₂] at h
      have hl:(Fin.last m).succ=Fin.last (m+1):=Fin.ext rfl
      rw [hprefix (Fin.last m),hl,hlast]
      exact h
    · obtain ⟨e,he₁,he₂⟩:=C.property.2.1 i
      have h:=hER e
      rw [he₁,he₂] at h
      have hi:i.castSucc.succ=i.succ.castSucc:=by apply Fin.ext;rfl
      rw [hprefix i.castSucc,hi,hprefix i.succ]
      exact h
  refine ⟨p,hp,hlen,?_,?_,?_⟩
  · rw [hsupp]
    exact finite_sequence_dropLast_of_prefix m f C.val hprefix
  · rw [finite_sequence_walk_edge_set G (m+1) f p hlen hsupp]
    unfold markedCyclePhysicalEdges
    apply Finset.image_congr
    intro i hi
    exact (marked_wheel_physical_edge_order tail head ktail khead m b π C f hprefix hlast i).symm
  · intro k hk
    have hk':k<m+1:=by simpa [hlen] using hk
    have hv:∀j:Fin ((m+1)+1),p.getVert j.val=f j:=by
      intro j
      have hh:some (p.getVert j.val)=p.support[j.val]? :=p.getVert_eq_support_getElem? (by omega)
      rw [hsupp] at hh
      simpa only [List.getElem?_ofFn,dif_pos (show j.val<(m+1)+1 by omega),Option.some.injEq] using hh
    have hh:=hdir ⟨k,hk'⟩
    change R (f ⟨k,by omega⟩) (f ⟨k+1,by omega⟩) at hh
    simpa only [←hv ⟨k,by omega⟩,←hv ⟨k+1,by omega⟩] using hh
end Oberwolfach
