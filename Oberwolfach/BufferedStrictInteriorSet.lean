module

public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! The strict indexed interior is the full vertex image with the two
endpoints removed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_single_strict_interior_eq
    {X:Type} [DecidableEq X] (n:ℕ) (inner:Fin (n+1)↪X):
    ((Finset.univ.filter (fun p:Fin (n+1)=>0<p.val ∧ p.val<n)).image inner)=
      (Finset.univ.image inner)\{inner 0,inner (Fin.last n)}:=by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
    Finset.mem_insert,Finset.mem_singleton,not_or]
  constructor
  · rintro ⟨p,⟨hp0,hpn⟩,rfl⟩
    refine ⟨⟨p,rfl⟩,?_,?_⟩
    · intro he
      have hh:=inner.injective he
      have hv:=congrArg Fin.val hh
      simp only [Fin.val_zero] at hv
      omega
    · intro he
      have hh:=inner.injective he
      have hv:=congrArg Fin.val hh
      simp only [Fin.val_last] at hv
      omega
  · rintro ⟨⟨p,rfl⟩,h0,hn⟩
    refine ⟨p,⟨?_,?_⟩,rfl⟩
    · by_contra h
      have hp:p=0:=Fin.ext (by simp only [Fin.val_zero];omega)
      exact h0 (congrArg inner hp)
    · by_contra h
      have hp:p=Fin.last n:=Fin.ext (by simp only [Fin.val_last];have hp:=p.isLt;omega)
      exact hn (congrArg inner hp)
end Oberwolfach
