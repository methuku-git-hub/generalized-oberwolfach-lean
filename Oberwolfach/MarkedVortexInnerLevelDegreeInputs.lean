module

public import Oberwolfach.MarkedFixedVortexInnerDegrees

@[expose] public section
/-! Actual inner degree inputs for each level, with a single explicit error
and estimates for every parent vertex, including vertices outside the inner set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_level_degree_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8)
    (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (alphaInner x:ℝ) (ha:alphaInner≤α/4) (hbx:β≤x)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let errParent:=β*I.card
      (∀ v:W,|(((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset v∩I).card:ℝ)-
        2*J.card/initialIndexDensity U D|≤errParent) ∧
      (∀ v:W,(1/2+2*alphaInner)*I.card≤
        (((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset v∩I).card:ℝ)) ∧
      errParent≤x*Fintype.card W:=by
  intro i hi W I J errParent
  obtain ⟨hmin,hregular,_,_⟩:=marked_vortex_fixed_inner_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hm i (by omega)
  have hcard:(I.card:ℝ)≤Fintype.card W:=by exact_mod_cast (Finset.card_le_univ I)
  have hx:0≤x:=hb.trans hbx
  refine ⟨hregular,?_,?_⟩
  · intro v
    have hh:=mul_le_mul_of_nonneg_right (show (1/2+2*alphaInner:ℝ)≤1/2+α/2 by linarith) (Nat.cast_nonneg I.card)
    exact hh.trans (hmin v)
  · exact (mul_le_mul_of_nonneg_right hbx (Nat.cast_nonneg I.card)).trans (mul_le_mul_of_nonneg_left hcard hx)
end Oberwolfach
