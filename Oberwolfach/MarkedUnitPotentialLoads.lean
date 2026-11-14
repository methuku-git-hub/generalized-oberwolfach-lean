module

public import Oberwolfach.TypedMarkedPotentialResources
public import Oberwolfach.TypedCycleClassLoads

@[expose] public section

/-! Potential spoke loads over a single formal hub are exactly ordered
cycle sums with the tested typed vertex omitted. Rim indicators are all
retained: the omitted root is a spoke, never a rim edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}

def markedUnitWheel (C:MarkedCycleTuple tail head ktail khead m π b):
    MarkedWheel tail head ktail khead m π b (fun (_:V) (_:Unit)=>True) (fun _ _=>True):=
  ⟨C,⟨(),trivial,fun _=>trivial⟩⟩

def markedUnitWheelEquiv:
    MarkedCycleTuple tail head ktail khead m π b≃
      MarkedWheel tail head ktail khead m π b (fun (_:V) (_:Unit)=>True) (fun _ _=>True) where
  toFun:=markedUnitWheel
  invFun:=Sigma.fst
  left_inv _:=rfl
  right_inv W:=by
    rcases W with ⟨C,⟨u,hu⟩⟩
    cases u
    rfl

theorem marked_unit_spoke_mem (C:MarkedCycleTuple tail head ktail khead m π b) (j:Bool) (v:V):
    (Sum.inr (j,v,()):(E⊕K)⊕(Bool×V×Unit))∈typedMarkedOccurrenceResources (markedUnitWheel C)↔
      (j,v)∈typedMarkedCycleVertices C:=by
  rw [typedMarkedOccurrenceResources_spoke]
  simp only [typedMarkedCycleVertices,Finset.mem_image,Finset.mem_univ,true_and,
    Prod.mk.injEq,markedUnitWheel,markedPositionType,and_true]

theorem marked_unit_omitted_condition
    (C:MarkedCycleTuple tail head ktail khead m π b) (R:E⊕K→Prop) (H:Bool→V→Unit→Prop) (j:Bool) (v:V):
    (∀ e∈typedMarkedOccurrenceResources (markedUnitWheel C),e≠Sum.inr (j,v,())→
      Sum.elim R (fun a:Bool×V×Unit=>H a.1 a.2.1 a.2.2) e)↔
      (∀ e,CanonicalMarkedArcMem C e→R e)∧
      ∀ x∈typedMarkedCycleVertices C,x≠(j,v)→H x.1 x.2 ():=by
  constructor
  · intro h
    constructor
    · intro e he
      exact h (Sum.inl e) ((typedMarkedOccurrenceResources_rim _ e).mpr he) (by simp)
    · rintro ⟨k,w⟩ hw hne
      apply h (Sum.inr (k,w,())) ((marked_unit_spoke_mem C k w).mpr hw)
      intro he
      apply hne
      exact Prod.ext (congrArg (fun x:Bool×V×Unit=>x.1) (Sum.inr.inj he))
        (congrArg (fun x:Bool×V×Unit=>x.2.1) (Sum.inr.inj he))
  · rintro ⟨hr,hs⟩ e he hne
    cases e with
    | inl e=>exact hr e ((typedMarkedOccurrenceResources_rim _ e).mp he)
    | inr x=>
      rcases x with ⟨k,w,u⟩
      cases u
      apply hs (k,w) ((marked_unit_spoke_mem C k w).mp he)
      intro h
      apply hne
      exact congrArg (fun x:Bool×V=>Sum.inr (x.1,x.2,())) h

theorem marked_unit_potential_load
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (R:E⊕K→Prop) (H:Bool→V→Unit→Prop) (j:Bool) (v:V):
    typedMarkedPotentialLoad (H₀:=fun (_:V) (_:Unit)=>True) (Hₖ:=fun _ _=>True) (fun W=>w W.1) R H (Sum.inr (j,v,()))=
      ∑ C,if (j,v)∈typedMarkedCycleVertices C∧(∀ e,CanonicalMarkedArcMem C e→R e)∧
        (∀ x∈typedMarkedCycleVertices C,x≠(j,v)→H x.1 x.2 ()) then w C else 0:=by
  unfold typedMarkedPotentialLoad resourceRootOmittedLoad
  rw [←Equiv.sum_comp markedUnitWheelEquiv]
  apply Finset.sum_congr rfl
  intro C hC
  simp only [markedUnitWheelEquiv,Equiv.coe_fn_mk]
  rw [marked_unit_spoke_mem,marked_unit_omitted_condition]
  split_ifs <;> rfl

end Oberwolfach
