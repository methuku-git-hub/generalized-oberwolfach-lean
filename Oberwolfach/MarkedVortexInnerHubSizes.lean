module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The inner hub set has the required lower density and is no larger than
the independently rounded inner vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_hub_sizes
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (hm:0<m) (ωI:ℝ) (hω:ωI≤ρ₀/8)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      ωI*I.card≤(J.card:ℝ) ∧ J.card≤I.card:=by
  intro i hi I J
  have hs:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hb hb1 he hm i (by omega)
  have hDpos:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith only [hn',hD])
  have hupper:=Q.index_size_upper hreg hn hDpos he.le hρhi (i:=i+1) (by omega)
  obtain ⟨hI,_,hJ,_⟩:=marked_vortex_inner_cardinalities Q i
  rw [Q.extendedVertices_eq (by omega:i+1≤Q.length)] at hI
  rw [Q.extendedIndices_eq (by omega:i+1≤Q.length)] at hJ
  constructor
  · exact (mul_le_mul_of_nonneg_right hω (Nat.cast_nonneg _)).trans hs.2.1
  · rw [hI,hJ]
    omega
end Oberwolfach
