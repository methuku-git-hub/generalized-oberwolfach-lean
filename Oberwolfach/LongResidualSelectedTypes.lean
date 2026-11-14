module

public import Oberwolfach.LongResidualSelectedStateSupply

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance selectedTypesDecEq : DecidableEq V := Classical.decEq V

theorem long_residual_selected_state_type_inclusions
    (G Small Bad:SimpleGraph V) (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ):
    let P:=longResidualHostArc M Small Bad
    let S₀:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1)
    let S₁:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1)
    let T₁:=longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Bad
    let T₀:Finset {e:V×V // P e}:=Finset.univ\T₁
    S₀⊆T₀ ∧ S₁=T₁:=by
  intro P S₀ S₁ T₁ T₀
  constructor
  · intro e he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro he1
    have h0:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he).2
    have h1:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 e.val.1 e.val.2=1:=(Finset.mem_filter.mp he1).2
    have hh0:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(0,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at h0
    have hh1:G.Adj e.val.1 e.val.2 ∧ ω (Sum.inl s(e.val.1,e.val.2))=(1,orientationBit e.val.1 e.val.2):=by
      by_contra h;simp [sampledColourOrientation,h] at h1
    have heq:(0:Fin 6)=1:=by simpa using congrArg Prod.fst (hh0.2.symm.trans hh1.2)
    exact (by decide : (0:Fin 6)≠1) heq
  · rfl
end Oberwolfach
