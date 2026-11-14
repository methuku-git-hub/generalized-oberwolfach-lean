module

public import Oberwolfach.FirstVortexEventAuxiliaryChoices
public import Oberwolfach.LongReferenceHostMargin

@[expose] public section
/-! The two event constructions can share the vortex tolerance and size
threshold, with graph-order bounds chosen afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reference_matching_vortex_thresholds
    (αRef βMatch βParent εBal εRef:ℝ)
    (hα:0<αRef) (hM:0<βMatch) (hP:0<βParent) (hBal:0<εBal) (hRef:0<εRef):
    ∃ βQ:ℝ,0<βQ ∧ βQ≤1/4 ∧ βQ≤αRef/4 ∧ βQ≤βMatch ∧ βQ≤βParent ∧
      βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
      ∀ mMatch mParent:ℕ,∃m:ℕ,1≤m ∧ mMatch≤m ∧ mParent≤m ∧
      ∀ nMatch nParent:ℕ,∃N:ℕ,∀n:ℕ,N≤n→m≤n ∧ nMatch≤n ∧ nParent≤n := by
  obtain ⟨β,hβ,hquarter,hαcap,hcap,hbal,href⟩:=
    first_vortex_reference_beta_choice αRef (min βMatch βParent) εBal εRef hα (by positivity) hBal hRef
  refine ⟨β,hβ,hquarter,hαcap,hcap.trans (min_le_left _ _),hcap.trans (min_le_right _ _),hbal,href,?_⟩
  intro mMatch mParent
  let m:=max 1 (max mMatch mParent)
  refine ⟨m,by dsimp [m];omega,by dsimp [m];omega,by dsimp [m];omega,?_⟩
  intro nMatch nParent
  refine ⟨max m (max nMatch nParent),?_⟩
  intro n hn
  exact ⟨(le_max_left _ _).trans hn,((le_max_left _ _).trans (le_max_right _ _)).trans hn,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn⟩
/-- If the reference-event margin is outside its permitted range, the
regular host required by the matching construction cannot exist. -/
theorem long_reference_matching_margin_dichotomy (αRef:ℝ):
    2*αRef≤1 ∨
      ∀ (V:Type) [Fintype V] (P:SimpleGraph V) (D:ℕ),
        P.IsRegularOfDegree D → 0<Fintype.card V →
        (1/2+2*αRef)*Fintype.card V≤(D:ℝ) → False := by
  by_cases h:2*αRef≤1
  · exact Or.inl h
  · right
    intro V _ P D hreg hn hmin
    have hhost:=long_reference_host_margin_le_half P D (2*αRef) hreg hn hmin
    linarith
end Oberwolfach
