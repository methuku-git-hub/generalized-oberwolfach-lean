module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! An arbitrary fixed local size threshold is met at every genuine vortex
    level once the terminal parameter is sufficiently large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_parent_size_threshold (ε:ℝ) (hε:0<ε) (N:ℕ):
    ∃M:ℕ,1≤M ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m),
      M≤m→∀i:ℕ,i<Q.length→N≤Fintype.card (markedVortexVertexType Q i) :=by
  let M:=max 1 ⌈(2*(N:ℝ))/ε⌉₊
  refine ⟨M,by dsimp [M];omega,?_⟩
  intro V U _ _ _ _ P D m β Q hm i hi
  have hM:(2*(N:ℝ))/ε≤(m:ℝ):=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈(2*(N:ℝ))/ε⌉₊≤m by dsimp [M] at hm;omega))
  have hmul:2*(N:ℝ)≤(m:ℝ)*ε:=(div_le_iff₀ hε).mp hM
  have hterm:(ε/2)*(m:ℝ)≤((Q.vertices Q.length).card:ℝ):=by
    have hh:=Q.terminal_lower
    nlinarith only [hh]
  have hsub:Q.vertices Q.length⊆Q.vertices i:=
    finset_chain_subset Q.vertices Q.length Q.nested (by omega) (le_refl _)
  have hcard:((Q.vertices Q.length).card:ℝ)≤(Q.vertices i).card:=by exact_mod_cast Finset.card_le_card hsub
  have hparent:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  rw [hparent]
  have hN:(N:ℝ)≤(Q.vertices i).card:=by nlinarith only [hmul,hterm,hcard]
  exact_mod_cast hN
end Oberwolfach
