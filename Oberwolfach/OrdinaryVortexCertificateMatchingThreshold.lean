module

public import Oberwolfach.OrdinaryVortexCertificateUniformThreshold
public import Oberwolfach.OrdinaryInitialConflictBudgetEventually

@[expose] public section
/-! One pre-sample size threshold simultaneously absorbs the matching's
fixed conflict loss and the wheel certificate's local conflict budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_certificate_matching_threshold
    (ε ρ₀ kcap Lconf η:ℝ) (d Nbase:ℕ)
    (hε:0<ε) (hρ:0<ρ₀) (hkcap:0<kcap) (hη:0<η):
    ∃M:ℕ,1≤M ∧ Nbase≤M ∧ 4/ε≤(M:ℝ) ∧
    (∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*η*n→cost+2*((3*d:ℕ):ℝ)≤15*η*n) ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<mv→
      (M:ℝ)≤ε*mv/2→∀(Q:Vortex U P D β ε mv) (i:ℕ),i<Q.length→
      let I:=markedVortexInnerVertices Q i;
      I.Nonempty ∧ Nbase≤I.card ∧ M≤I.card ∧
        Lconf≤kcap^2*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) :=by
  obtain ⟨Nmatch,hmatch⟩:=ordinary_initial_conflict_budget_eventually d η hη
  obtain ⟨M,hM,hbase,hfour,hlevel⟩:=ordinary_vortex_certificate_uniform_threshold ε ρ₀ kcap Lconf hε hρ hkcap (max Nbase Nmatch)
  have hbaseM:Nbase≤M:=(le_max_left _ _).trans hbase
  have hmatchM:Nmatch≤M:=(le_max_right _ _).trans hbase
  refine ⟨M,hM,hbaseM,hfour,?_,?_⟩
  · intro n hn cost hcost
    exact hmatch n (hmatchM.trans hn) cost hcost
  · intro V U _ _ _ _ P D mv β hreg hn hD hρlo hρhi hβ hβ1 hmv hterminal Q i hi I
    have hh:=hlevel V U P D mv β hreg hn hD hρlo hρhi hβ hβ1 hmv hterminal Q i hi
    exact ⟨hh.1,(le_max_left Nbase Nmatch).trans hh.2.1,hh.2.2.1,hh.2.2.2⟩
end Oberwolfach
