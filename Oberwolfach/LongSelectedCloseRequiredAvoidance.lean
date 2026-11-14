module

public import Oberwolfach.LongPreparationPhysicalContainment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance selectedCloseAvoidanceDecEq : DecidableEq V := Classical.decEq V

/-- If every selected close edge has a marked reference direction and the
corrected class orientation preserves it, the required close graph cannot
consume selected edges. -/
theorem long_selected_close_required_avoids_reference
    (S Sel Used:SimpleGraph V) (I:Finset V) (π:Equiv.Perm V) (d:ℕ) (Mhost:V→V→ℕ) (RMark:V→V→Prop)
    (hSelected:∀x y,Sel.Adj x y→PermutationClose π (3*d) x y→RMark x y ∨ RMark y x)
    (hDirection:∀x∈I,∀y∈I,RMark x y→Mhost x y=1)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0):
    let D:=fun x y=>Mhost x y=1 ∧ ¬RMark x y
    ∀x∈I,∀y∈I,Sel.Adj x y→¬(longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)).Adj x y:=by
  intro D x hx y hy hSel hK
  obtain ⟨hS,hClose,hD⟩:=hK
  rcases hSelected x y hSel hClose with hm|hm
  · have hM:=hDirection x hx y hy hm
    rcases hD with hD|hD
    · exact hD.1.2 hm
    · have hh:=hphysical x y
      have hrev:=hD.1.1
      rw [if_pos hS,hM,hrev] at hh
      omega
  · have hM:=hDirection y hy x hx hm
    rcases hD with hD|hD
    · have hh:=hphysical x y
      have hfor:=hD.1.1
      rw [if_pos hS,hM,hfor] at hh
      omega
    · exact hD.1.2 hm
end Oberwolfach
