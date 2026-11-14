module

public import Oberwolfach.LongDualInitialMarked
public import Oberwolfach.LongSelectedTypedRawDirection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance dualReferenceDecEq : DecidableEq V := Classical.decEq V

theorem long_dual_initial_agrees_with_selected_types
    (G Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (Mhost:V→V→ℕ):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G ω Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    ∀e:{a:V×V // P a},
      (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω x)) false e.val.1 e.val.2=1→e∉T₁) ∧
      (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω x)) true e.val.1 (π.symm e.val.2)=1→e∈T₁):=by
  intro P T₁ e
  constructor
  · intro hOrd hT
    have hraw:=(long_selected_ordinary_raw_direction G π d ω e.val.1 e.val.2 hOrd)
    have hraw1:sampledColourOrientation G ω 1 e.val.1 e.val.2≠1:=by
      intro h
      have h0:G.Adj e.val.1 e.val.2 ∧ ω s(e.val.1,e.val.2)=(0,orientationBit e.val.1 e.val.2):=by
        by_contra hn;simp [sampledColourOrientation,hn] at hraw
      have h1:G.Adj e.val.1 e.val.2 ∧ ω s(e.val.1,e.val.2)=(1,orientationBit e.val.1 e.val.2):=by
        by_contra hn;simp [sampledColourOrientation,hn] at h
      have heq:(0:Fin 6)=1:=by simpa using congrArg Prod.fst (h0.2.symm.trans h1.2)
      exact (by decide : (0:Fin 6)≠1) heq
    rcases (Finset.mem_filter.mp hT).2 with h|h
    · exact hraw1 h.1
    · exact h hraw.2
  · intro hMark
    have hraw:=long_selected_marked_raw_direction G π d ω e.val.1 e.val.2 hMark
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Or.inl hraw⟩
end Oberwolfach
