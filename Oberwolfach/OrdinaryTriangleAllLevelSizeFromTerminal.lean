module

public import Oberwolfach.OrdinaryVortexLocalSizeInputs

@[expose] public section
/-! One terminal-size bound supplies the selected reference threshold at
every level and the common inner certificate size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_all_level_size_from_terminal
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε ρ₀:ℝ) (Q:Vortex U P D β ε mv)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hmv:0<mv)
    (N₀ M:ℕ) (hN:N₀≤M) (hsize:2/ε≤(M:ℝ)) (hterminal:(M:ℝ)≤ε*mv/2):
    ∀i,i<Q.length→N₀≤Fintype.card (markedVortexVertexType Q i) ∧ M≤(markedVortexInnerVertices Q i).card :=by
  intro i hi
  have hs:=ordinary_vortex_local_size_inputs Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hmv i hi M M le_rfl hsize hterminal
  have hcard:(markedVortexInnerVertices Q i).card≤Fintype.card (markedVortexVertexType Q i):=Finset.card_le_univ _
  exact ⟨hN.trans (hs.2.1.trans hcard),hs.2.1⟩
end Oberwolfach
