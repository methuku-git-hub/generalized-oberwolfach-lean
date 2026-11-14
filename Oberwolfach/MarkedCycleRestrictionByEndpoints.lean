module

public import Oberwolfach.MarkedUnitPotentialLoads
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section

/-! Restrict the rim identifiers using injectivity of each directed
endpoint map. Global physical injectivity is not needed on the universe
of potential arcs, where it would generally be false. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}

theorem markedCycle_restrict_iff_endpoints (PE : E → Prop) (PK : K → Prop)
    (hinj : Function.Injective (fun e:E=>(tail e,head e)))
    (hkinj : Function.Injective (fun e:K=>(ktail e,khead e)))
    (C : MarkedCycleTuple tail head ktail khead m π b) :
    IsMarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b C.val ↔
        ∀ i,Sum.elim PE PK (markedCycleTypedEdge tail head ktail khead m π b C i) := by
  constructor
  · intro h i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · obtain ⟨e,he⟩ := h.2.2
      have hh := Classical.choose_spec C.property.2.2
      have heq : Classical.choose C.property.2.2=e.val := hkinj (Prod.ext (hh.1.trans he.1.symm) (hh.2.trans he.2.symm))
      simpa only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr,heq] using e.property
    · obtain ⟨e,he⟩ := h.2.1 j
      have hh := Classical.choose_spec (C.property.2.1 j)
      have heq : Classical.choose (C.property.2.1 j)=e.val := hinj (Prod.ext (hh.1.trans he.1.symm) (hh.2.trans he.2.symm))
      simpa only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl,heq] using e.property
  · intro h
    refine ⟨C.property.1,?_,?_⟩
    · intro j
      have hj := h j.castSucc
      simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl] at hj
      exact ⟨⟨Classical.choose (C.property.2.1 j),hj⟩,Classical.choose_spec (C.property.2.1 j)⟩
    · have hj := h (Fin.last m)
      simp only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr] at hj
      exact ⟨⟨Classical.choose C.property.2.2,hj⟩,Classical.choose_spec C.property.2.2⟩


def markedCycleRestrictionByEndpointsEquiv (PE:E→Prop) (PK:K→Prop)
    (hinj:Function.Injective (fun e:E=>(tail e,head e)))
    (hkinj:Function.Injective (fun e:K=>(ktail e,khead e))):
    {C:MarkedCycleTuple tail head ktail khead m π b // ∀ e,CanonicalMarkedArcMem C e→Sum.elim PE PK e}≃
      MarkedCycleTuple (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b where
  toFun C:=⟨C.val.val,(markedCycle_restrict_iff_endpoints PE PK hinj hkinj C.val).mpr
    (fun i=>C.property _ ⟨i,rfl⟩)⟩
  invFun C:=⟨markedCycleToLarger PE PK C,by
    rintro e ⟨i,rfl⟩
    exact (markedCycle_restrict_iff_endpoints PE PK hinj hkinj (markedCycleToLarger PE PK C)).mp C.property i⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem marked_restricted_typed_root_load
    (PE:E→Prop) (PK:K→Prop)
    (hinj:Function.Injective (fun e:E=>(tail e,head e)))
    (hkinj:Function.Injective (fun e:K=>(ktail e,khead e)))
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (keep:Bool×V→Prop) (root:Bool×V):
    resourceRootOmittedLoad typedMarkedCycleVertices (fun C=>w (markedCycleToLarger PE PK C)) keep root=
      ∑ C,if root∈typedMarkedCycleVertices C∧(∀ e,CanonicalMarkedArcMem C e→Sum.elim PE PK e)∧
        (∀ x∈typedMarkedCycleVertices C,x≠root→keep x) then w C else 0:=by
  let Survives:=fun C:MarkedCycleTuple tail head ktail khead m π b=>∀ e,CanonicalMarkedArcMem C e→Sum.elim PE PK e
  let f:=fun C:MarkedCycleTuple tail head ktail khead m π b=>
    if root∈typedMarkedCycleVertices C∧Survives C∧(∀ x∈typedMarkedCycleVertices C,x≠root→keep x) then w C else 0
  have he:=finite_sum_restrict_of_zero Survives f (by intro C hC;simp only [f,hC,false_and,and_false,ite_false])
  change _=∑ C,f C
  rw [he]
  unfold resourceRootOmittedLoad
  rw [←Equiv.sum_comp (markedCycleRestrictionByEndpointsEquiv PE PK hinj hkinj)]
  apply Finset.sum_congr (by ext; simp)
  intro C _
  have hv:typedMarkedCycleVertices ((markedCycleRestrictionByEndpointsEquiv PE PK hinj hkinj) C)=
      typedMarkedCycleVertices C.val:=rfl
  rw [hv]
  dsimp only [f]
  simp only [show Survives C.val from C.property, true_and]
  split_ifs <;> rfl

end Oberwolfach
