module

public import Oberwolfach.OrdinaryTriangleNumericCoreThresholdMonotone
public import Oberwolfach.OrdinaryTriangleAllLevelSizeFromTerminal
public import Oberwolfach.OrdinaryVortexCertificateMatchingThresholdAtSize

@[expose] public section
/-! Enlarge the wheel threshold once to cover the reference, initial matching
and all selected pre-host sizes, while retaining the same certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_common_certificate_size_choice
    (β ε ρ₀ α pmin εrows tpot lamInner:ℝ) (d k:ℕ)
    (ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub:ℝ)
    (p βeGeo βhGeo ν cap τ eps ellCap ηBudget:ℝ)
    (Msmall vCert N₀ Ncert Nextra vOuter vInner vExtra:ℕ)
    (hε:0<ε) (hρ:0<ρ₀) (hη:0<ηBudget)
    (hcert:OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
      ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap Msmall vCert):
    ∃M vCommon:ℕ,1≤M ∧ Msmall≤M ∧ N₀≤M ∧ Ncert≤M ∧ Nextra≤M ∧ 2/ε≤(M:ℝ) ∧
      (∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*ηBudget*n→cost+2*((3*d:ℕ):ℝ)≤15*ηBudget*n) ∧
      vCert≤vCommon ∧ vOuter≤vCommon ∧ vInner≤vCommon ∧ vExtra≤vCommon ∧
      OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
        ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap M vCommon ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<mv→
      (M:ℝ)≤ε*mv/2→∀(Q:Vortex U P D β ε mv) i,i<Q.length→
        N₀≤Fintype.card (markedVortexVertexType Q i) ∧ M≤(markedVortexInnerVertices Q i).card :=by
  let Nbase:=max Msmall (max N₀ (max Ncert Nextra))
  obtain ⟨M,hM,hbase,hfour,_hconf,hmatch,_hgeometry⟩:=
    ordinary_vortex_certificate_matching_threshold_at_size ε ρ₀ 1 0 ηBudget d Nbase hε hρ (by norm_num) hη
  have hSmall:Msmall≤M:=(le_max_left _ _).trans hbase
  have hN₀:N₀≤M:=((le_max_left _ _).trans (le_max_right _ _)).trans hbase
  have hNcert:Ncert≤M:=(((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hbase
  have hNextra:Nextra≤M:=(((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hbase
  have htwo:2/ε≤(M:ℝ):=by
    have hpos:0≤(1/ε:ℝ):=by positivity
    have h2:2/ε=2*(1/ε):=by ring
    have h4:4/ε=4*(1/ε):=by ring
    linarith only [hfour,hpos,h2,h4]
  let vCommon:=max vCert (max vOuter (max vInner vExtra))
  have hvCert:vCert≤vCommon:=le_max_left _ _
  have hvOuter:vOuter≤vCommon:=(le_max_left _ _).trans (le_max_right _ _)
  have hvInner:vInner≤vCommon:=((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hvExtra:vExtra≤vCommon:=((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hcert':=ordinary_triangle_numeric_core_threshold_monotone β ε ρ₀ α pmin εrows tpot lamInner d k
    ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap Msmall vCert M vCommon hSmall hvCert hcert
  refine ⟨M,vCommon,hM,hSmall,hN₀,hNcert,hNextra,htwo,hmatch,hvCert,hvOuter,hvInner,hvExtra,hcert',?_⟩
  intro V U _ _ _ _ P D mv hreg hn hD hρlo hρhi hβ hβ1 hmv hterminal Q i hi
  exact ordinary_triangle_all_level_size_from_terminal P D mv β ε ρ₀ Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hmv N₀ M hN₀ htwo hterminal i hi
end Oberwolfach
