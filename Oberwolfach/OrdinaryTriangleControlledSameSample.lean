module

public import Oberwolfach.OrdinaryTriangleControlledFromSample

@[expose] public section
/-! The actual packing, cleanup and triangle finish yield the controlled
level step on the same event, with the same probability bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_controlled_cover_down_same_sample
    (μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
    (Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
    (σ:Ω→Sym2 (V⊕U)→Bool) (p τ ν:ℝ)
    (hprob:1-e≤μ.probability (fun a=>E a∧OrdinaryPackingCleanupFinishOutcome (Q a) (F a) (H a) (X a) (Z a) (σ a) p τ ν))
    (hbal:∀a,E a→∀v,(Q a).degree v=2*(Finset.univ.filter (H a v)).card)
    (hdiv:∀a,E a→∀u,3∣(Finset.univ.filter (fun v=>H a v u)).card):
    1-e≤μ.probability (fun a=>E a∧OrdinaryTriangleControlledCoverDownResult (Q a) (H a) (X a) (Z a)
      ((ν+4*p)*Fintype.card (V⊕U))):=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro a ha
  exact ⟨ha.1,ordinary_triangle_controlled_cover_down_from_sample_outcome (Q a) (F a) (H a) (X a) (Z a)
    (σ a) p τ ν (hbal a ha.1) (hdiv a ha.1) ha.2⟩
end Oberwolfach
