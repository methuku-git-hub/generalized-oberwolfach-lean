module

public import Oberwolfach.OrdinaryInitialPlacementRateObstruction

@[expose] public section

/-! The current whole-hub-set load estimate is incompatible with the
initial-edit hierarchy; this concerns sufficient estimates, not the theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_hub_capacity_obstruction
    (ε ρ₀ δinitial η δplacement:ℝ)
    (hε:0<ε) (hρ:0<ρ₀) (hδi:δinitial≤1)
    (hsmall:15*η≤min δinitial (δinitial*(ρ₀/8))*ε/2)
    (hδp:0≤δplacement) (hδp1:δplacement≤1)
    (hcap:5*Real.sqrt δplacement≤η)
    (hHubs:ρ₀*ε/16≤δplacement/2):False :=by
  have hrate:δplacement≤η:=ordinary_sqrt_cap_controls_residual_rate δplacement η hδp hδp1 hcap
  have hmin:min δinitial (δinitial*(ρ₀/8))≤δinitial*(ρ₀/8):=min_le_right _ _
  have hscaled:=mul_le_mul_of_nonneg_right hmin hε.le
  have hδρ:=mul_le_mul_of_nonneg_right hδi (show 0≤ρ₀/8 by positivity)
  have hδρε:=mul_le_mul_of_nonneg_right hδρ hε.le
  have hp:0<ρ₀*ε:=mul_pos hρ hε
  nlinarith only [hsmall,hscaled,hδρε,hrate,hHubs,hp]

theorem ordinary_first_vortex_hubs_force_capacity_rate
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε ρ₀ δ:ℝ) (Q:Vortex U P D β ε mv)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv)
    (hHubs:((Q.extendedIndices 1).card:ℝ)≤δ*Fintype.card V/2):
    ρ₀*ε/16≤δ/2 :=by
  have hinner:(ε/2)*(Fintype.card V:ℝ)≤(Q.extendedVertices 1).card:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    have hh:=(Q.consecutive_size_bounds hε hm Q.length_pos).1
    rw [Q.initial] at hh
    simp only [Finset.card_univ] at hh
    nlinarith
  have hindex:(ρ₀/8)*(Q.extendedVertices 1).card≤(Q.extendedIndices 1).card:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega),
      Q.extendedIndices_eq (by have hh:=Q.length_pos;omega)]
    exact Q.index_size_lower hreg hn hD hρ hρlo hβ hβ1 (by have hh:=Q.length_pos;omega)
  have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hmul:=mul_le_mul_of_nonneg_left hinner (show 0≤ρ₀/8 by positivity)
  by_contra h
  have hh:0<(ρ₀*ε/16-δ/2)*(Fintype.card V:ℝ):=mul_pos (by linarith) hn'
  nlinarith only [hmul,hindex,hHubs,hh]
end Oberwolfach
