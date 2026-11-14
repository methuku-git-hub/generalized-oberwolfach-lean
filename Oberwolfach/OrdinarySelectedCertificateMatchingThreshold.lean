module

public import Oberwolfach.OrdinaryVortexCertificateMatchingThresholdAtSize
public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad

@[expose] public section
/-! Select one threshold for the chosen certificate, the matching loss,
and every level of the later protected history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_certificate_matching_threshold
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad)
    (ε ρ₀ kcap η:ℝ) (d Nfinish Nextra:ℕ)
    (hε:0<ε) (hρ:0<ρ₀) (hkcap:0<kcap) (hη:0<η):
    let Nbase:=max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)
    ∃M:ℕ,1≤M ∧ Nbase≤M ∧ Nextra≤M ∧ 4/ε≤(M:ℝ) ∧ s.L≤kcap^2*M ∧
    (∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*η*n→cost+2*((3*d:ℕ):ℝ)≤15*η*n) ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<mv→
      (M:ℝ)≤ε*mv/2→∀(Q:Vortex U P D β ε mv) (i:ℕ),i<Q.length→
      let I:=markedVortexInnerVertices Q i;
      I.Nonempty ∧ Nbase≤I.card ∧ M≤I.card ∧
        s.L≤kcap^2*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) :=by
  intro Nbase
  obtain ⟨M,hM,hbase,hfour,hbudget,hconf,hlevel⟩:=
    ordinary_vortex_certificate_matching_threshold_at_size ε ρ₀ kcap s.L η d (max Nbase Nextra) hε hρ hkcap hη
  refine ⟨M,hM,(le_max_left _ _).trans hbase,(le_max_right _ _).trans hbase,hfour,hbudget,hconf,?_⟩
  intro V U _ _ _ _ P D mv β hreg hn hD hρlo hρhi hβ hβ1 hmv hterminal Q i hi I
  have hh:=hlevel V U P D mv β hreg hn hD hρlo hρhi hβ hβ1 hmv hterminal Q i hi
  exact ⟨hh.1,(le_max_left Nbase Nextra).trans hh.2.1,hh.2.2.1,hh.2.2.2⟩
end Oberwolfach
