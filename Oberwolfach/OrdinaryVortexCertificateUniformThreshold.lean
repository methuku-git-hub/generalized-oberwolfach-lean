module

public import Oberwolfach.OrdinaryCertificateCommonSizeThreshold
public import Oberwolfach.OrdinaryVortexLocalSizeInputs

@[expose] public section
/-! One threshold, chosen before the host and sample, supplies both the
certificate size and its fixed conflict budget at every vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_certificate_uniform_threshold
    (ε ρ₀ kcap Lconf:ℝ) (hε:0<ε) (hρ:0<ρ₀) (hkcap:0<kcap) (Nbase:ℕ):
    ∃M:ℕ,1≤M ∧ Nbase≤M ∧ 4/ε≤(M:ℝ) ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<mv→
      (M:ℝ)≤ε*mv/2→∀(Q:Vortex U P D β ε mv) (i:ℕ),i<Q.length→
      let I:=markedVortexInnerVertices Q i;
      I.Nonempty ∧ Nbase≤I.card ∧ M≤I.card ∧
        Lconf≤kcap^2*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) :=by
  obtain ⟨M,hM,hbase,hfour,hbudget⟩:=ordinary_certificate_common_size_threshold Lconf kcap ε hkcap hε Nbase
  refine ⟨M,hM,hbase,hfour,?_⟩
  intro V U _ _ _ _ P D mv β hreg hn hD hρlo hρhi hβ hβ1 hmv hterminal Q i hi I
  have htwo:2/ε≤(M:ℝ):=by
    have h1:0≤(1/ε:ℝ):=by positivity
    have h2:2/ε=2*(1/ε):=by ring
    have h4:4/ε=4*(1/ε):=by ring
    linarith only [hfour,h1,h2,h4]
  have hsize:=ordinary_vortex_local_size_inputs Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hmv i hi
    M M (le_refl _) htwo hterminal
  refine ⟨hsize.1,hbase.trans hsize.2.1,hsize.2.1,?_⟩
  exact ordinary_certificate_budget_at_inner_size I M Lconf kcap hsize.2.1 hbudget
end Oberwolfach
