module

public import Oberwolfach.MarkedVortexTerminalDecompositionGeometry
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section
/-! Fixed absorber reserves fit both deletion budgets once the original host
is large; the initial vortex level has exactly the original vertex order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_terminal_budget
    (e:ℕ) (γ σ:ℝ) (hγ:0<γ) (hσ:0<σ):
    ∃N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
      N≤Fintype.card V→
      (e:ℝ)≤γ*Fintype.card (markedVortexVertexType Q 0) ∧
      (e:ℝ)≤σ*Fintype.card (markedVortexVertexType Q 0) :=by
  obtain ⟨Nγ,hNγ⟩:=eventually_constant_le_linear e γ hγ
  obtain ⟨Nσ,hNσ⟩:=eventually_constant_le_linear e σ hσ
  refine ⟨max Nγ Nσ,?_⟩
  intro V U _ _ _ G D m β ε Q hN
  have hcard:Fintype.card (markedVortexVertexType Q 0)=Fintype.card V:=by
    change Fintype.card ↥(Q.extendedVertices 0)=Fintype.card V
    rw [Fintype.card_coe,Q.extendedVertices_eq (Nat.zero_le _),Q.initial,Finset.card_univ]
  rw [hcard]
  exact ⟨hNγ _ (le_trans (le_max_left _ _) hN),hNσ _ (le_trans (le_max_right _ _) hN)⟩
end Oberwolfach
