module

public import Oberwolfach.OrdinaryFixedVortexNonrootUniformMarginsDeltaCap
public import Oberwolfach.OrdinaryNonrootCoverNumericInputs

@[expose] public section
/-! Package the numerical hypotheses of the actual nonroot wheel-cover
constructor directly from the fixed-vortex estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_nonroot_numeric_inputs
    (ρ₀ pmin href δlimit a ρ θ aLoad:ℝ) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hhref:0<href)
    (hδlimit:0<δlimit) (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (haLoad:0<aLoad):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀β:ℝ,0≤β→β≤1/4→∀d Nextra:ℕ,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (i:ℕ),i<Q.length→
    ∀(pH εR εH Ledit:ℝ),pmin≤pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→
      Ledit≤ζlimit*(markedVortexInnerVertices Q i).card→
    OrdinaryNonrootNumericInputs
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexDeeperVertices Q i)
      (markedVortexInnerHubs Q i) (markedVortexDeeperHubs Q i) Nextra d
      (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href := by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hmain⟩:=
    ordinary_fixed_vortex_nonroot_uniform_margins_delta_cap ρ₀ pmin href δlimit a ρ θ aLoad hρ₀ hpmin hhref hδlimit ha hρ hθ haLoad
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,?_⟩
  intro ε hε hεvortex β hβ hβ1 d Nextra
  obtain ⟨v₀,hv₀,hmain⟩:=hmain ε hε hεvortex β hβ hβ1 d Nextra
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
  exact hmain V U P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
end Oberwolfach
