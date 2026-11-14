module

public import Oberwolfach.OrdinaryInducedColourCutProjection
public import Oberwolfach.SampledColourLargeCuts
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! A fixed induced rim inherits its colour-orientation cut event from the
    very same independent ambient physical-edge states. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_colour_cut_probability
    (α pstar:ℝ) (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (q₀:ℕ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],∀(P:SimpleGraph V) (I:Finset V),N≤I.card→
      (∀v:I,(1/2+α)*I.card≤((P.induce (I:Set V)).degree v:ℝ))→
    ∀(ρ:Fin 2→ℝ) (hρ:∀a,0≤ρ a) (hsum:∑a,ρ a=1),pstar≤ρ 0→
    1-1/(I.card:ℝ)^q₀≤(FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
      (fun σ=>OrdinaryInducedRimCutEvent I (sampledColourOrientation P σ 0) α pstar):=by
  obtain ⟨N,hN⟩:=sampledColourOrientation_large_cuts α pstar hα hα1 hpstar 2 q₀
  refine ⟨N,?_⟩
  intro V _ _ P I hn hP ρ hρ hsum hp
  have hP':∀v:I,(1/2+α)*Fintype.card I≤((P.induce (I:Set V)).degree v:ℝ):=by
    intro v
    simp only [Fintype.card_coe]
    convert hP v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hlocal:=hN I (by simpa only [Fintype.card_coe] using hn) (P.induce (I:Set V)) hP' ρ hρ hsum
  simp only [Fintype.card_coe] at hlocal
  let μ:=FiniteLaw.pi (fun _:Sym2 I=>FiniteLaw.categoricalDirection ρ hρ hsum)
  let Good:=fun σ:Sym2 I→Fin 2×Bool=>∀a:Fin 2,pstar≤ρ a→∀S T:Finset I,
    (1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card→
    (α*pstar/64)*I.card*min (S.card:ℝ) T.card≤
      (matrixCut (sampledColourOrientation (P.induce (I:Set V)) σ a) S T:ℝ)
  let Goal:=fun σ:Sym2 I→Fin 2×Bool=>∀S T:Finset I,
    (1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card→
    (α*pstar/64)*I.card*min (S.card:ℝ) T.card≤
      (matrixCut (sampledColourOrientation (P.induce (I:Set V)) σ 0) S T:ℝ)
  have hGood:1-1/(I.card:ℝ)^q₀≤μ.probability Good:=by
    convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hmono:μ.probability Good≤μ.probability Goal:=
    finiteLaw_probability_mono μ Good Goal (fun σ hσ=>hσ 0 hp)
  have hproj:=ordinary_induced_colour_cut_projection P I α pstar ρ hρ hsum
  have hout:1-1/(I.card:ℝ)^q₀≤μ.probability Goal:=hGood.trans hmono
  exact hproj.symm ▸ hout
end Oberwolfach
