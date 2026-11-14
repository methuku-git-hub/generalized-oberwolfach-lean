module

public import Oberwolfach.OrdinaryInducedRimEvent
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.RandomColourCuts

@[expose] public section
/-! Project the independent ambient coloured edge law exactly to the
    induced rim event on a fixed inner subtype. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_colour_cut_projection
    {V:Type} [Fintype V] [LinearOrder V] (P:SimpleGraph V) (I:Finset V) (α pstar:ℝ)
    (ρ:Fin 2→ℝ) (hρ:∀a,0≤ρ a) (hsum:∑a,ρ a=1):
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
        (fun σ=>OrdinaryInducedRimCutEvent I (sampledColourOrientation P σ 0) α pstar)=
    (FiniteLaw.pi (fun _:Sym2 I=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
      (fun σ=>∀S T:Finset I,
        (1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card→
        (α*pstar/64)*I.card*min (S.card:ℝ) T.card≤
          (matrixCut (sampledColourOrientation (P.induce (I:Set V)) σ 0) S T:ℝ)):=by
  let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let f:Sym2 I→Sym2 V:=Sym2.map φ
  have hf:Function.Injective f:=Sym2.map.injective φ.injective
  let μ:=fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum
  let Local:=fun σ:Sym2 I→Fin 2×Bool=>∀S T:Finset I,
    (1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card→
    (α*pstar/64)*I.card*min (S.card:ℝ) T.card≤
      (matrixCut (sampledColourOrientation (P.induce (I:Set V)) σ 0) S T:ℝ)
  have hp:=finiteLaw_pi_injective_projection_event μ f hf Local
  calc
    _ = (FiniteLaw.pi μ).probability (fun σ=>Local (fun e=>σ (f e))):=by
      apply congrArg (FiniteLaw.probability (FiniteLaw.pi μ))
      funext σ
      apply propext
      have he:=ordinary_induced_sampled_colour_orientation P I σ (0:Fin 2)
      dsimp only [Local,OrdinaryInducedRimCutEvent]
      rw [he]
    _ = _:=hp
end Oberwolfach
