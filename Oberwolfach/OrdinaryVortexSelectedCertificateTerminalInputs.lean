module

public import Oberwolfach.OrdinarySelectedCertificateMatchingThreshold
public import Oberwolfach.OrdinaryMatchingBudgetFromVortexInner

@[expose] public section
/-! The terminal size selected before the sample supplies the same local
certificate size and matching budget at every actual vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_selected_certificate_terminal_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad)
    (ρ₀ kcap η:ℝ) (d N₀ Nfinish M N:ℕ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hhalf:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hmv:0<mv)
    (hbase:max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)≤M)
    (hN₀:N₀≤M) (hfour:4/ε≤(M:ℝ)) (hMN:M≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (hbudget:s.L≤kcap^2*M)
    (hmatch:∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*η*n→cost+2*((3*d:ℕ):ℝ)≤15*η*n):
    s.Ncert≤N ∧ 2/ε≤(N:ℝ) ∧ s.L≤kcap^2*M ∧
    ∀i,i<Q.length→
      N₀≤Fintype.card (markedVortexVertexType Q i) ∧
      M≤(markedVortexInnerVertices Q i).card ∧
      (∀cost:ℝ,cost≤14*η*Fintype.card V→cost+2*((3*d:ℕ):ℝ)≤15*η*Fintype.card V) :=by
  have hcertM:s.Ncert≤M:=by omega
  have htwo:2/ε≤(M:ℝ):=by
    have hone:0≤(1/ε:ℝ):=by positivity
    have h2:2/ε=2*(1/ε):=by ring
    have h4:4/ε=4*(1/ε):=by ring
    linarith only [hfour,hone,h2,h4]
  have hMNreal:(M:ℝ)≤N:=by exact_mod_cast hMN
  have hMterminal:(M:ℝ)≤ε*mv/2:=hMNreal.trans hterminal
  refine ⟨hcertM.trans hMN,htwo.trans hMNreal,hbudget,?_⟩
  intro i hi
  have hsize:=ordinary_vortex_local_size_inputs Q hreg hn hhalf hρ hρlo hρhi hβ hβ1 hε hmv i hi
    M M (le_refl _) htwo hMterminal
  have hcard:(markedVortexInnerVertices Q i).card≤Fintype.card (markedVortexVertexType Q i):=Finset.card_le_univ _
  refine ⟨hN₀.trans (hsize.2.1.trans hcard),hsize.2.1,?_⟩
  intro cost hcost
  exact ordinary_matching_budget_from_vortex_inner Q i M d η cost hmatch hsize.2.1 hcost
end Oberwolfach
