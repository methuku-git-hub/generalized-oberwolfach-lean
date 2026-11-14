module

public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Exact wheel decompositions can be restricted to a typed subhost when
all their physical resources belong to that subhost. Physical injectivity
identifies each rim identifier; spoke restrictions preserve its given type.
This also transfers decompositions between two subhosts of one ambient host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

def markedSubhostResources (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (PE:E→Prop) (PK:K→Prop) (PS:V×U→Prop):Finset (Finset V⊕(V×U)):=
  (Finset.univ.filter (Sum.elim PE PK)).image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
    (Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧PS z)).image Sum.inr

theorem marked_wheel_survives_subhost
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (PE:E→Prop) (PK:K→Prop) (PS:V×U→Prop)
    (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (hW:markedWheelPhysicalResources W⊆markedSubhostResources tail head ktail khead π H₀ HK PE PK PS):
    MarkedWheelSurvives PE PK (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u)) W:=by
  have ha (i:Fin (m+1)):Sum.elim PE PK (markedCycleTypedEdge tail head ktail khead m π b W.1 i):=by
    have he:Sum.inl (markedPhysicalEdge tail head ktail khead π
      (markedCycleTypedEdge tail head ktail khead m π b W.1 i))∈markedWheelPhysicalResources W:=by
      apply (markedWheelPhysicalResources_rim W _).mpr
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hh:=hW he
    rcases Finset.mem_union.mp hh with hh|hh
    · obtain ⟨a,ha,heq⟩:=Finset.mem_image.mp hh
      have heq':a=markedCycleTypedEdge tail head ktail khead m π b W.1 i:=hp (Sum.inl.inj heq)
      exact heq' ▸ (Finset.mem_filter.mp ha).2
    · obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hh
      exact (Sum.inr_ne_inl hz).elim
  have hs (i:Fin (m+1)):PS (W.1.val i,W.2.val):=by
    have he:Sum.inr (W.1.val i,W.2.val)∈markedWheelPhysicalResources W:=by
      apply (markedWheelPhysicalResources_spoke W _ _).mpr
      exact ⟨rfl,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    rcases Finset.mem_union.mp (hW he) with hh|hh
    · obtain ⟨a,_,heq⟩:=Finset.mem_image.mp hh
      exact (Sum.inl_ne_inr heq).elim
    · obtain ⟨z,hz,heq⟩:=Finset.mem_image.mp hh
      exact (Sum.inr.inj heq) ▸ (Finset.mem_filter.mp hz).2.2
  refine ⟨⟨W.1.property.1,?_,?_⟩,⟨W.2.property.1,hs 0⟩,?_⟩
  · intro j
    have hj:=ha j.castSucc
    simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl] at hj
    exact ⟨⟨Classical.choose (W.1.property.2.1 j),hj⟩,Classical.choose_spec (W.1.property.2.1 j)⟩
  · have hj:=ha (Fin.last m)
    simp only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr] at hj
    exact ⟨⟨Classical.choose W.1.property.2.2,hj⟩,Classical.choose_spec W.1.property.2.2⟩
  · intro j
    exact ⟨W.2.property.2 j,hs j.succ⟩

theorem marked_decomposition_restrict_to_subhost
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (PE:E→Prop) (PK:K→Prop) (PS:V×U→Prop) (S:Finset (Finset V⊕(V×U)))
    (hS:S⊆markedSubhostResources tail head ktail khead π H₀ HK PE PK PS)
    (hdec:HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W) S):
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b
        (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u))=>markedWheelPhysicalResources W) S:=by
  obtain ⟨M,hM,hcover⟩:=hdec
  have hw (W:M):MarkedWheelSurvives PE PK (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u)) W.val:=by
    apply marked_wheel_survives_subhost hp PE PK PS W.val
    apply Finset.Subset.trans _ hS
    rw [←hcover]
    exact resource_subset_union markedWheelPhysicalResources M W.val W.property
  let f:=fun W:M=>(⟨⟨W.val.1.val,(hw W).1⟩,⟨W.val.2.val,(hw W).2⟩⟩:
    MarkedWheel (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b
      (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u)))
  have hr (W:M):markedWheelPhysicalResources (f W)=markedWheelPhysicalResources W.val:=by
    exact (markedWheelToLarger_resources PE PK (fun _ _ h=>h.1) (fun _ _ h=>h.1) (f W)).symm
  refine ⟨Finset.univ.image f,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨W,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Z,_,rfl⟩:=Finset.mem_image.mp hZ
    simpa only [hr] using hM W.val W.property Z.val Z.property (fun he=>hne (congrArg f (Subtype.ext he)))
  · rw [←hcover]
    ext e
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨W,⟨Z,rfl⟩,he⟩
      exact ⟨Z.val,Z.property,by rwa [hr] at he⟩
    · rintro ⟨W,hW,he⟩
      exact ⟨f ⟨W,hW⟩,⟨⟨W,hW⟩,rfl⟩,by rwa [hr]⟩

theorem marked_decomposition_transfer_subhosts
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (BE RE:E→Prop) (BK RK:K→Prop) (BS RS:V×U→Prop) (S:Finset (Finset V⊕(V×U)))
    (hS:S⊆markedSubhostResources tail head ktail khead π H₀ HK RE RK RS)
    (hdec:HasResourceDecomposition
      (fun W:MarkedWheel (fun e:{e // BE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // BK e}=>ktail e.val) (fun e=>khead e.val) m π b
        (fun v u=>H₀ v u∧BS (v,u)) (fun v u=>HK v u∧BS (v,u))=>markedWheelPhysicalResources W) S):
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:{e // RE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // RK e}=>ktail e.val) (fun e=>khead e.val) m π b
        (fun v u=>H₀ v u∧RS (v,u)) (fun v u=>HK v u∧RS (v,u))=>markedWheelPhysicalResources W) S:=by
  apply marked_decomposition_restrict_to_subhost hp RE RK RS S hS
  exact resource_decomposition_map _ _
    (markedWheelToLarger BE BK (fun _ _ h=>h.1) (fun _ _ h=>h.1))
    (markedWheelToLarger_resources BE BK (fun _ _ h=>h.1) (fun _ _ h=>h.1)) S hdec

end Oberwolfach
