module

public import Oberwolfach.UniformFiberCounts

@[expose] public section
/-! Count one fixed index and one fixed length in a dependent family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sigma_key_class_count {U:Type} [Fintype U] [DecidableEq U]
    (D:U→Type) [∀u,Fintype (D u)] [∀u,DecidableEq (D u)]
    (len:∀u,D u→ℕ) (u:U) (r:ℕ):
    (Finset.univ.filter (fun z:Σu,D u=>z.1=u ∧ len z.1 z.2=r)).card =
      (Finset.univ.filter (fun x:D u=>len u x=r)).card :=by
  symm
  apply Finset.card_bij (fun x _=>⟨u,x⟩)
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    exact hx
  · intro x hx y hy hxy
    exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
  · rintro ⟨v,x⟩ hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx
    obtain ⟨hv,hx⟩:=hx
    subst v
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
end Oberwolfach
