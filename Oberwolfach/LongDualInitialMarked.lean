module

public import Oberwolfach.LongEligibleMarkedIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance dualInitialDecEq : DecidableEq V := Classical.decEq V

noncomputable def longDualInitialMarked
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Small:SimpleGraph V)
    (Ord Mark:V×V→Prop):Finset {e:V×V // longEligibleResidualArc M Small ⊥ e}:=
  Finset.univ.filter (fun e=>(sampledColourOrientation G ω 1 e.val.1 e.val.2=1 ∧ Mark e.val) ∨ ¬Ord e.val)

theorem long_dual_initial_marked_membership
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Small:SimpleGraph V)
    (Ord Mark:V×V→Prop) (v x:V):
    x∈markedCandidateIncomingTails (longEligibleResidualArc M Small ⊥)
      (longDualInitialMarked G ω M Small Ord Mark) v ↔
      ((sampledColourOrientation G ω 1 x v=1 ∧ Mark (x,v)) ∨ ¬Ord (x,v)) ∧
        longEligibleResidualArc M Small ⊥ (x,v) :=by
  constructor
  · intro hx
    obtain ⟨e,he,hx⟩:=Finset.mem_image.mp hx
    have hh:=(Finset.mem_filter.mp he)
    have hs:=(Finset.mem_filter.mp hh.1).2
    have heq:e.val=(x,v):=Prod.ext hx hh.2
    simpa only [heq] using And.intro hs e.property
  · rintro ⟨hsel,hq⟩
    refine Finset.mem_image.mpr ⟨⟨(x,v),hq⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsel⟩,rfl⟩
end Oberwolfach
