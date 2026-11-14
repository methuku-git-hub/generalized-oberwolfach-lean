module

public import Oberwolfach.OrdinaryFixedVortexInnerCycleWeights
public import Oberwolfach.OrdinaryFixedVortexHubSetups
public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry

@[expose] public section
/-! A single early choice of coefficient bounds and a terminal-size threshold
provides fixed fractional cycle weights and all hub setups before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_hub_setups_before_sampling
    (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀(β ε ρ₀ pmin ξ b Bweight ηHub Kdom:ℝ),
      0≤β→β≤1/4→β≤α/8→0<ε→ε<1/4→0<ρ₀→0<pmin→pmin≤1→
      2/ε≤Kdom→b≤c→(4*C/pmin^(3*m+1))*Kdom^m≤Bweight→ξ+2*β<ηHub→
    ∀d:ℕ,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (θhost pR pH:ℝ),1/2≤θhost→cycleThreshold (m+1)≤θhost→
      (θhost+α)*Fintype.card V≤D→pmin≤pR→pR≤1→pmin≤pH→pH≤1→
      pR=initialIndexDensity U D*pH→
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    ∀i,i<Q.length→
      OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (weight i) pmin pR pH
        (2*pH*(markedVortexInnerHubs Q i).card/pR) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom:=by
  obtain ⟨c,C,hc,hC,hweights⟩:=ordinary_fixed_vortex_inner_cycle_weights m hm α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro β ε ρ₀ pmin ξ b Bweight ηHub Kdom hβ hβ1 hβα hε hε1 hρ₀ hpmin hpmin1 hK hb hB hgap d
  let gap:ℝ:=ηHub-ξ-2*β
  have hgap':0<gap:=by dsimp [gap];linarith
  let Cfix:ℝ:=12*((m+1:ℕ):ℝ)^4*C*(2*((3*d:ℕ):ℝ))
  have hCfix:0≤Cfix:=by dsimp [Cfix];positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (Cfix/gap)
  let N₀:=max N 1
  obtain ⟨vWeights,hvWeights,hweights⟩:=hweights β ε ρ₀ hβ hβ1 (by linarith) hε hε1 hρ₀
  obtain ⟨vSizes,hvSizes,hsize⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ N₀
  refine ⟨max vWeights vSizes,by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ θhost pR pH hθ hthreshold hdegree
    hpR hpR1 hpH hpH1 hpEq
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith)
      (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  obtain ⟨weight,hweight⟩:=hweights V U P D vsize hreg hn hDhalf hρlo hρhi (by omega) Q θhost hthreshold hdegree
  have herr:∀i,i<Q.length→ξ+2*β+12*((m+1:ℕ):ℝ)^4*C*(2*((3*d:ℕ):ℝ))/
      (markedVortexInnerVertices Q i).card≤ηHub:=by
    intro i hi
    have hs:=hsize V U P D vsize hreg hn hDhalf hρlo hρhi (by omega) Q i hi
    have hI:N₀≤(markedVortexInnerVertices Q i).card:=hs.2.2.1
    have hIpos:(0:ℝ)<(markedVortexInnerVertices Q i).card:=by
      exact_mod_cast (show 0<(markedVortexInnerVertices Q i).card by dsimp [N₀] at hI;omega)
    have hNr:(N:ℝ)≤(markedVortexInnerVertices Q i).card:=by
      exact_mod_cast (show N≤(markedVortexInnerVertices Q i).card by dsimp [N₀] at hI;omega)
    have hcap:Cfix≤gap*(markedVortexInnerVertices Q i).card:=by
      have hh: Cfix<gap*(N:ℝ):=by
        have hh':= (div_lt_iff₀ hgap').mp hN
        nlinarith only [hh']
      have ht:=mul_le_mul_of_nonneg_left hNr hgap'.le
      linarith
    have hratio:Cfix/(markedVortexInnerVertices Q i).card≤gap:=
      (div_le_iff₀ hIpos).mpr (by nlinarith only [hcap])
    dsimp [Cfix,gap] at hratio
    linarith only [hratio]
  refine ⟨weight,?_⟩
  exact ordinary_fixed_vortex_hub_setups m d P D vsize β ε θhost α ρ₀ pmin pR pH ξ c C b Bweight ηHub Kdom
    Q π hπ hreg hn hθ hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hε (by omega) hpmin hpmin1 hpR hpR1 hpH hpH1 hpEq
    hc hC.le hK hb hB weight hweight herr
end Oberwolfach
