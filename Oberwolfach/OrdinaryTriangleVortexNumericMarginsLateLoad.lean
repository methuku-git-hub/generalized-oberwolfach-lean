module

public import Oberwolfach.OrdinaryFixedVortexNonrootNumericInputsLateLoad
public import Oberwolfach.OrdinaryVortexTriangleConflictSizeThreshold

@[expose] public section
/-! The numerical inputs for the separated triangle cover follow uniformly
from the fixed vortex once its scale and terminal-size threshold are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_vortex_numeric_margins_separated_late_load
    (ρ₀ pmin href δlimit b ρrow:ℝ)
    (hρ₀:0<ρ₀) (hpmin:0<pmin) (hhref:0<href) (hδlimit:0<δlimit)
    (hb:0<b) (hρrow:0<ρrow):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀a:ℝ,0<a→∀β:ℝ,0≤β→β≤1/4→∀d Nextra:ℕ,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (i:ℕ),i<Q.length→
    ∀(pH εR εH Ledit:ℝ),pmin≤pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→
      Ledit≤ζlimit*(markedVortexInnerVertices Q i).card→
    OrdinaryNonrootNumericInputs
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexDeeperVertices Q i)
      (markedVortexInnerHubs Q i) (markedVortexDeeperHubs Q i) Nextra d
      (ρ₀/8) b b b a ζlimit ε δcut ζcut εcut pH εR εH Ledit href ∧
      (((2*(3*d):ℕ):ℝ)+2*(3*d:ℕ))≤ρrow*Fintype.card (markedVortexVertexType Q i)/2 :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hnum⟩:=
    ordinary_fixed_vortex_nonroot_numeric_inputs_late_load ρ₀ pmin href δlimit b b b hρ₀ hpmin hhref hδlimit hb hb hb
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,?_⟩
  intro ε hε hεvortex a ha β hβ hβ1 d Nextra
  obtain ⟨v₁,hv₁,hnum⟩:=hnum ε hε hεvortex a ha β hβ hβ1 d Nextra
  obtain ⟨v₂,hv₂,hconf⟩:=ordinary_vortex_triangle_conflict_size_threshold β ε ρ₀ ρrow d hβ hβ1 hε (hεvortex.trans_lt hεv1) hρ₀ hρrow
  refine ⟨max v₁ v₂,by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
  exact ⟨hnum V U P D vsize hreg hn hD hρlo hρhi (le_trans (le_max_left _ _) hv) Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL,
    hconf V U P D vsize hreg hn hD hρlo hρhi (le_trans (le_max_right _ _) hv) Q i hi⟩
end Oberwolfach
