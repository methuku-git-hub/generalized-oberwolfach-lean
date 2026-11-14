module

public import Oberwolfach.MarkedUnitPotentialLoads

@[expose] public section

/-! A spoke-root potential sum over all formal hubs is exactly the cycle
sum at its specified hub. The root is omitted, whether present or absent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}

def markedFullWheel (C:MarkedCycleTuple tail head ktail khead m π b) (u:U):
    MarkedWheel tail head ktail khead m π b (fun (_:V) (_:U)=>True) (fun _ _=>True):=
  ⟨C,⟨u,trivial,fun _=>trivial⟩⟩

def markedFullWheelEquiv:
    (MarkedCycleTuple tail head ktail khead m π b×U)≃
      MarkedWheel tail head ktail khead m π b (fun (_:V) (_:U)=>True) (fun _ _=>True) where
  toFun x:=markedFullWheel x.1 x.2
  invFun W:=(W.1,W.2.val)
  left_inv _:=rfl
  right_inv _:=rfl

theorem marked_full_spoke_mem (C:MarkedCycleTuple tail head ktail khead m π b) (u t:U) (j:Bool) (v:V):
    (Sum.inr (j,v,u):(E⊕K)⊕(Bool×V×U))∈typedMarkedOccurrenceResources (markedFullWheel C t)↔
      t=u∧(j,v)∈typedMarkedCycleVertices C:=by
  rw [typedMarkedOccurrenceResources_spoke]
  simp only [markedFullWheel,typedMarkedCycleVertices,Finset.mem_image,Finset.mem_univ,true_and,
    markedPositionType,Prod.mk.injEq]
  tauto

theorem marked_full_omitted_condition
    (C:MarkedCycleTuple tail head ktail khead m π b) (R:E⊕K→Prop) (H:Bool→V→U→Prop)
    (j:Bool) (v:V) (u:U):
    (∀ e∈typedMarkedOccurrenceResources (markedFullWheel C u),e≠Sum.inr (j,v,u)→
      Sum.elim R (fun a:Bool×V×U=>H a.1 a.2.1 a.2.2) e)↔
      (∀ e,CanonicalMarkedArcMem C e→R e)∧
      ∀ x∈typedMarkedCycleVertices C,x≠(j,v)→H x.1 x.2 u:=by
  constructor
  · intro h
    constructor
    · intro e he
      exact h (Sum.inl e) ((typedMarkedOccurrenceResources_rim _ e).mpr he) (by simp)
    · rintro ⟨k,w⟩ hw hne
      apply h (Sum.inr (k,w,u)) ((marked_full_spoke_mem C u u k w).mpr ⟨rfl,hw⟩)
      intro he
      apply hne
      exact Prod.ext (congrArg (fun x:Bool×V×U=>x.1) (Sum.inr.inj he))
        (congrArg (fun x:Bool×V×U=>x.2.1) (Sum.inr.inj he))
  · rintro ⟨hr,hs⟩ e he hne
    cases e with
    | inl e=>exact hr e ((typedMarkedOccurrenceResources_rim _ e).mp he)
    | inr x=>
      rcases x with ⟨k,w,t⟩
      have ht:=(marked_full_spoke_mem C t u k w).mp he
      rcases ht with ⟨rfl,ht⟩
      apply hs (k,w) ht
      intro h
      apply hne
      exact congrArg (fun x:Bool×V=>Sum.inr (x.1,x.2,u)) h

theorem marked_full_potential_spoke
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (R:E⊕K→Prop) (H:Bool→V→U→Prop)
    (j:Bool) (v:V) (u:U):
    typedMarkedPotentialLoad (H₀:=fun (_:V) (_:U)=>True) (Hₖ:=fun _ _=>True)
      (fun W=>w W.1) R H (Sum.inr (j,v,u))=
      ∑ C,if (j,v)∈typedMarkedCycleVertices C∧(∀ e,CanonicalMarkedArcMem C e→R e)∧
        (∀ x∈typedMarkedCycleVertices C,x≠(j,v)→H x.1 x.2 u) then w C else 0:=by
  unfold typedMarkedPotentialLoad resourceRootOmittedLoad
  rw [←Equiv.sum_comp markedFullWheelEquiv,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single u]
  · simp only [markedFullWheelEquiv,Equiv.coe_fn_mk,marked_full_spoke_mem,true_and,
      marked_full_omitted_condition]
    split_ifs <;> rfl
  · intro t _ htu
    simp only [markedFullWheelEquiv,Equiv.coe_fn_mk,marked_full_spoke_mem,htu,false_and,ite_false]
  · simp

end Oberwolfach
