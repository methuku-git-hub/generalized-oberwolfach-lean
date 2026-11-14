module

public import Oberwolfach.OrdinaryTriangleSeparatedNumericScalesCapped
public import Oberwolfach.OrdinaryTriangleVortexNumericMarginsLateLoad
public import Oberwolfach.OrdinaryTriangleVortexCoverRate

@[expose] public section
/-! Choose the triangle geometry before the vortex ratio and its load after
that ratio, obtaining uniform numeric inputs and next-level cover costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_vortex_cover_rate_hierarchy
    (ρ₀ p γ θ ρ ρhub η href δlimit δrate cap:ℝ)
    (hρ₀:0<ρ₀) (hp:0<p) (hγ:0<γ) (hθ:0<θ) (hρ:0<ρ) (hρhub:0<ρhub) (hη:0<η)
    (hhref:0<href) (hδlimit:0<δlimit) (hδrate:0<δrate) (hcap:0<cap):
    ∃b δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<b ∧ b≤cap ∧ 0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧
      0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ εvortex≤b ∧ εvortex≤ρ₀/16 ∧
      6*b≤p^6*γ/4 ∧ 6*b≤(p^6*γ/4)*(ρ₀/16) ∧
      b≤p^6*γ/8 ∧ b≤(p^6*γ/8)*(ρ₀/16) ∧ b≤θ ∧ 2*b≤(ρ₀/16)*p*η ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∃a:ℝ,0<a ∧ a≤cap ∧ a≤1 ∧
      b+12*a≤ρhub ∧ 3*b+24*a≤ρ/2 ∧
    ∀β:ℝ,0≤β→β≤1/4→∀d Nextra:ℕ,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (i:ℕ),i<Q.length→
    ∀(pH εR εH Ledit:ℝ),p≤pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→
      Ledit≤ζlimit*(markedVortexInnerVertices Q i).card→
    OrdinaryNonrootNumericInputs
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexDeeperVertices Q i)
      (markedVortexInnerHubs Q i) (markedVortexDeeperHubs Q i) Nextra d
      (ρ₀/8) b b b a ζlimit ε δcut ζcut εcut pH εR εH Ledit href ∧
      (((2*(3*d):ℕ):ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card (markedVortexVertexType Q i)/2 ∧
      18*a*Fintype.card (markedVortexVertexType Q i)+
        3*((markedVortexDeeperHubs Q i).card+(markedVortexDeeperVertices Q i).card)≤δrate*(markedVortexInnerVertices Q i).card ∧
      9*a*Fintype.card (markedVortexVertexType Q i)+3*((markedVortexDeeperVertices Q i).card:ℝ)≤δrate*(markedVortexInnerVertices Q i).card :=by
  obtain ⟨b,a₀,hb,hbcap,ha₀,ha₀cap,hLV,hLU,hI,hJ,hθb,hbal,hscale⟩:=
    ordinary_triangle_separated_numeric_scales_capped p γ (ρ₀/16) θ ρ ρhub η cap hp hγ (by positivity) hθ hρ hρhub hη hcap
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εv,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hnum⟩:=
    ordinary_triangle_vortex_numeric_margins_separated_late_load ρ₀ p href δlimit b ρ hρ₀ hp hhref hδlimit hb hρ
  let εvortex:=min εv (min (δrate/12) (min b (ρ₀/16)))
  have hεvortex:0<εvortex:=lt_min hεv (lt_min (by positivity) (lt_min hb (by positivity)))
  have hεvortex1:εvortex<1/4:=(min_le_left _ _).trans_lt hεv1
  refine ⟨b,δcut,ζcut,εcut,ζlimit,εsample,εvortex,hb,hbcap,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)),hLV,hLU,hI,hJ,hθb,hbal,?_⟩
  intro ε hε hεvortex
  have hεv:ε≤εv:=hεvortex.trans (min_le_left _ _)
  have hεrate:ε≤δrate/12:=hεvortex.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨a,ha,hacap,hrate⟩:=ordinary_triangle_vortex_cover_rate ε δrate (min a₀ 1)
    hε hδrate (lt_min ha₀ (by norm_num)) hεrate
  have ha₀':a≤a₀:=hacap.trans (min_le_left _ _)
  have ha1:a≤1:=hacap.trans (min_le_right _ _)
  obtain ⟨hbudget,hcaprow⟩:=hscale a ha.le ha₀'
  refine ⟨a,ha,ha₀'.trans ha₀cap,ha1,hbudget,hcaprow,?_⟩
  intro β hβ hβ1 d Nextra
  obtain ⟨v₀,hv₀,hnum⟩:=hnum ε hε hεv a ha β hβ hβ1 d Nextra
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
  obtain ⟨hinputs,hconf⟩:=hnum V U P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
  have hBI:(markedVortexInnerHubs Q i).card≤(markedVortexInnerVertices Q i).card:=hinputs.2.2.2.2.2.2.1
  have hm:0<vsize:=by omega
  obtain ⟨hrow,hcol⟩:=hrate V U P D vsize β Q hm i hi hBI
  exact ⟨hinputs,hconf,hrow,hcol⟩
end Oberwolfach
