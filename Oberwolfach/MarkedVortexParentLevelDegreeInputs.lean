module

public import Oberwolfach.MarkedFixedVortexParentDegrees

@[expose] public section
/-! Parent-level degree and degree-target inputs for every level of a fixed
vortex, with the original regularity error enlarged to the record tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_parent_level_degree_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤α/8)
    (hb1:β≤1/4) (he:0<ε) (hm:0<m) (κ:ℝ) (hbκ:β≤κ)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      (∀ x:W,(1/2+α/2)*(Fintype.card W:ℝ)≤
        ((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)) ∧
      (∀ x:W,|((G.comap (markedVortexVertexEmbedding Q i)).degree x:ℝ)-Dload|≤κ*Fintype.card W) ∧
      ((Fintype.card W:ℝ)/2≤Dload) ∧ Dload≤2*Fintype.card W:=by
  intro i hi W Z Dload
  obtain ⟨hmin,hregular,hlo,hhi⟩:=marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hm i (by omega)
  exact ⟨hmin,fun x=>(hregular x).trans (mul_le_mul_of_nonneg_right hbκ (Nat.cast_nonneg _)),hlo,hhi⟩
end Oberwolfach
