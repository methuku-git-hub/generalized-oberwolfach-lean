module

public import Oberwolfach.MarkedRootedPathCycles
public import Oberwolfach.MarkedCycleRotation

@[expose] public section

/-! A row wheel whose prescribed outgoing arc is marked. Its marked
spoke is at the first attachment, not at the row root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_wheel_with_marked_opening {V U E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (n : ℕ)
    (π : Equiv.Perm V) (b : ℕ) (H₀ HK : V → U → Prop)
    (v : V) (u : U) (p : Fin (n+1) → V)
    (hsep : PermutationSeparated π b (Fin.cons (α:=fun _=>V) v p))
    (hopen : ∃ e, ktail e=v ∧ khead e=p 0)
    (hclose : ∃ e, tail e=p (Fin.last n) ∧ head e=v)
    (hpath : ∀ i : Fin n, ∃ e, tail e=p i.castSucc ∧ head e=p i.succ)
    (hroot : H₀ v u) (hfirst : HK (p 0) u)
    (hfree : ∀ i, i≠0 → H₀ (p i) u) :
    ∃ W : MarkedWheel tail head ktail khead (n+1) π b H₀ HK,
      W.2.val=u ∧ ∀ i, W.1.val i=Fin.cons (α:=fun _=>V) v p (canonicalMarkedRotation 0 i) := by
  let z : Fin (n+2) ↪ V := ⟨Fin.cons (α:=fun _=>V) v p,permutationSeparated_injective π b _ hsep⟩
  have hO : ∀ i : Fin (n+2), i≠0 → ∃ e, tail e=z i ∧ head e=z (finRotate (n+2) i) := by
    intro i hi
    refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) i hi
    refine Fin.lastCases ?_ (fun k => ?_) j
    · have he : (Fin.last n).succ=Fin.last (n+1) := rfl
      simpa only [z,Function.Embedding.coeFn_mk,he,finRotate_last,Fin.cons_last,Fin.cons_zero] using hclose
    · have he : k.castSucc.succ=k.succ.castSucc := rfl
      have hv : Fin.cons (α:=fun _=>V) v p k.succ.castSucc=p k.castSucc := by
        rw [←he,Fin.cons_succ]
      simpa only [z,Function.Embedding.coeFn_mk,he,finRotate_castSucc_eq_succ,hv,Fin.cons_succ] using hpath k
  have hK : ∃ e, ktail e=z 0 ∧ khead e=z (finRotate (n+2) 0) := by
    have he : finRotate (n+2) (0 : Fin (n+2))=(0 : Fin (n+1)).succ :=
      finRotate_castSucc_eq_succ (n+1) 0
    simpa only [z,Function.Embedding.coeFn_mk,he,Fin.cons_zero,Fin.cons_succ] using hopen
  have hsK : HK (z (finRotate (n+2) 0)) u := by
    have he : finRotate (n+2) (0 : Fin (n+2))=(0 : Fin (n+1)).succ :=
      finRotate_castSucc_eq_succ (n+1) 0
    simpa only [z,Function.Embedding.coeFn_mk,he,Fin.cons_succ] using hfirst
  have hsO : ∀ i, i≠finRotate (n+2) 0 → H₀ (z i) u := by
    intro i
    refine Fin.cases (fun _ => hroot) (fun j hj => ?_) i
    apply hfree j
    intro he
    apply hj
    rw [he]
    exact (finRotate_castSucc_eq_succ (n+1) 0).symm
  exact marked_wheel_from_cyclic_embedding tail head ktail khead (n+1) π b H₀ HK
    z 0 u hsep hO hK hsK hsO

end Oberwolfach
