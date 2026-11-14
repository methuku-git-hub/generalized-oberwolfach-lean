module

public import Oberwolfach.MarkedHubFactorIntervalSeparation

@[expose] public section
/-! In a hub factor, every marked spoke selects a wheel rooted at that
marked vertex, provided ordinary and marked spokes are disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_root_selection
    {V U E K:Type*} [Fintype V] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V)
    (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (S Y:Finset V) (hcover:M.biUnion (hubMarkedCycleVertices u)=S)
    (hYS:Y⊆S) (hmarked:∀x∈Y,Hₖ x u) (hsep:∀x,Hₖ x u→¬H₀ x u):
    ∃select:{x // x∈Y}↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u,
      ∀x,select x∈M ∧ (select x).val 0=x.val := by
  have hexist:∀x:{x // x∈Y},∃C:HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u,
      C∈M ∧ C.val 0=x.val:=by
    intro x
    have hx:x.val∈M.biUnion (hubMarkedCycleVertices u):=by rw [hcover];exact hYS x.property
    obtain ⟨C,hCM,hxC⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hxC
    refine ⟨C,hCM,?_⟩
    by_cases hzero:i=0
    · simpa [hzero] using hi
    · obtain ⟨j,hj⟩:=Fin.eq_succ_of_ne_zero hzero
      have ho:H₀ x.val u:=by
        rw [←hi,hj]
        exact C.property.2.2 j
      exact (hsep x.val (hmarked x.val x.property) ho).elim
  let f:{x // x∈Y}→HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u:=fun x=>Classical.choose (hexist x)
  have hf:∀x,f x∈M ∧ (f x).val 0=x.val:=fun x=>Classical.choose_spec (hexist x)
  let select:{x // x∈Y}↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u:=
    ⟨f,by
      intro x y h
      apply Subtype.ext
      calc
        x.val=(f x).val 0:=(hf x).2.symm
        _=(f y).val 0:=congrArg (fun C=>C.val 0) h
        _=y.val:=(hf y).2⟩
  exact ⟨select,hf⟩
end Oberwolfach
