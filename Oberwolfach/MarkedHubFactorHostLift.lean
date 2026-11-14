module

public import Oberwolfach.MarkedHubFactorOn

@[expose] public section

/-! Lift a factor to a larger typed host using actual occurrence maps.
Cycle coordinates, spoke types and physical graphs are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K EB KB:Type} [Fintype V] [DecidableEq V]

def hubCycleHostLift
    (tail head:E→V) (ktail khead:K→V) (btail bhead:EB→V) (bktail bkhead:KB→V)
    (e:E→EB) (k:K→KB) (het:∀ a,btail (e a)=tail a) (heh:∀ a,bhead (e a)=head a)
    (hkt:∀ a,bktail (k a)=ktail a) (hkh:∀ a,bkhead (k a)=khead a)
    (m b:ℕ) (π:Equiv.Perm V) (H₀ HK B₀ BK:V→U→Prop)
    (h₀:∀ v u,H₀ v u→B₀ v u) (hK:∀ v u,HK v u→BK v u) (u:U):
    HubMarkedCycle tail head ktail khead m π b H₀ HK u↪
      HubMarkedCycle btail bhead bktail bkhead m π b B₀ BK u where
  toFun C:=⟨C.val,⟨C.property.1.1,
    fun i=>by obtain ⟨a,ha,hb⟩:=C.property.1.2.1 i;exact ⟨e a,(het a).trans ha,(heh a).trans hb⟩,
    by obtain ⟨a,ha,hb⟩:=C.property.1.2.2;exact ⟨k a,(hkt a).trans ha,(hkh a).trans hb⟩⟩,
    hK _ _ C.property.2.1,fun i=>h₀ _ _ (C.property.2.2 i)⟩
  inj' C D he:=Subtype.ext (congrArg (fun C:HubMarkedCycle btail bhead bktail bkhead m π b B₀ BK u=>C.val) he)

theorem marked_hub_factor_host_lift [Fintype U] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V) (btail bhead:EB→V) (bktail bkhead:KB→V)
    (e:E→EB) (k:K→KB) (het:∀ a,btail (e a)=tail a) (heh:∀ a,bhead (e a)=head a)
    (hkt:∀ a,bktail (k a)=ktail a) (hkh:∀ a,bkhead (k a)=khead a)
    (m b:ℕ) (π:Equiv.Perm V) (H₀ HK B₀ BK:V→U→Prop)
    (h₀:∀ v u,H₀ v u→B₀ v u) (hK:∀ v u,HK v u→BK v u) (u:U) (Y:Finset V)
    (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y):
    ∃ Q:MarkedHubFactorOn btail bhead bktail bkhead m π b B₀ BK u Y,
      Q.rim=P.rim∧Q.graph=P.graph:=by
  let f:=hubCycleHostLift tail head ktail khead btail bhead bktail bkhead e k het heh hkt hkh m b π H₀ HK B₀ BK h₀ hK u
  have hv (C):hubMarkedCycleVertices u (f C)=hubMarkedCycleVertices u C:=rfl
  have he (C):hubCyclePhysicalEdges u (f C)=hubCyclePhysicalEdges u C:=by
    unfold hubCyclePhysicalEdges markedCyclePhysicalEdges
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply,markedCycle_physical_pair,hubCycleAsMarked]
    rfl
  let Q:MarkedHubFactorOn btail bhead bktail bkhead m π b B₀ BK u Y:=
    {cycles:=P.cycles.image f
     disjoint:=by
      intro C hC D hD hCD
      obtain ⟨c,hc,hfc⟩:=Finset.mem_image.mp hC
      obtain ⟨d,hd,hfd⟩:=Finset.mem_image.mp hD
      subst C;subst D
      exact P.disjoint c hc d hd (fun h=>hCD (congrArg f h))
     covers:=by
      rw [Finset.image_biUnion]
      exact P.covers}
  have hr:Q.rim=P.rim:=by
    change physicalEdgeGraph ((P.cycles.image f).biUnion (hubCyclePhysicalEdges u))=P.rim
    rw [Finset.image_biUnion]
    simp_rw [he]
    rfl
  exact ⟨Q,hr,congrArg (fun G:SimpleGraph V=>G.map (Sum.inl:V→V⊕U)) hr⟩

end Oberwolfach
