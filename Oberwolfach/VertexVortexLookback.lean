module

public import Oberwolfach.VortexVertexSets
public import Oberwolfach.VortexSetSequenceLookback
public import Oberwolfach.NestedCountsLookback

@[expose] public section
/-! Strengthen the vortex degree estimates to any fixed lookback depth. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe a

structure VertexVortexLookback {V:Type a} [Fintype V] (G:SimpleGraph V)
    (D:ℕ) (η ε:ℝ) (m t:ℕ) extends VertexVortex G D η ε m where
  degrees_lookback:∀i≤length,0 < i →∀x∈vertices (i-(t+1)),
    |((G.neighborFinset x∩vertices i).card:ℝ)-((D:ℝ)/Fintype.card V)*(vertices i).card|≤η*(vertices i).card

theorem vertexVortex_lookback_exists {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) (he1 : ε < 1) (t:ℕ) (ht:1≤t) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ (V : Type a) [Fintype V] (G : SimpleGraph V) (D m : ℕ),
      G.IsRegularOfDegree D → m₀ ≤ m → m ≤ Fintype.card V →
      Nonempty (VertexVortexLookback G D η ε m t) := by
  obtain ⟨N₁, hN₁2, hN₁⟩ := vortex_set_sequence_lookback.{a} he he1 t
  obtain ⟨N₂, hN₂1, hN₂⟩ := eventually_vortex_error_budget (β := 2 * η)
    (ρ := 1) (by positivity) he he1 (by norm_num)
  refine ⟨max N₁ N₂, by omega, ?_⟩
  intro V _ G D m hreg hm hmn
  have hmpos : 0 < m := by omega
  obtain ⟨hlarge, hbudget, _⟩ := hN₂ m (by omega)
  have hbudget' : (m : ℝ) ^ (-1 / 3 : ℝ) / (1 - ε ^ (1 / 3 : ℝ)) ≤ η := by
    nlinarith [hbudget]
  obtain ⟨ℓ, hlpos, hlupper, hlbefore, hllower⟩ := floorOrbit_stopping he he1 hmpos hmn hlarge
  obtain ⟨B, hB0, hBcard, hBstep⟩ := hN₁ V Finset.univ (fun x => G.neighborFinset x) ℓ
    (by intro i hi; simpa only [Finset.card_univ] using (show N₁ ≤ floorOrbit ε (Fintype.card V) i from (by have := hlbefore i hi; omega)))
  have hcard : ∀ i ≤ ℓ, (B i).card = floorOrbit ε (Fintype.card V) i := by
    simpa only [Finset.card_univ] using hBcard
  have hsub : ∀ i < ℓ, B (i + 1) ⊆ B i := fun i hi => (hBstep i hi).1
  have hterminalLower:ε*m/2≤((B ℓ).card:ℝ):=by
    rw [hcard ℓ (by omega)]
    exact hllower ℓ (by omega)
  have hterminalUpper:(B ℓ).card<m:=by
    rw [hcard ℓ (by omega)]
    exact hlupper
  have hstrong:∀i≤ℓ,0 < i →∀x∈B (i-(t+1)),
      |((G.neighborFinset x∩B i).card:ℝ)-((D:ℝ)/Fintype.card V)*(B i).card|≤η*(B i).card:=by
    intro i hi hipos x hx
    have htel := nested_normalized_count_estimate_lookback B (fun x => G.neighborFinset x)
      (fun j => ((B j).card : ℝ) ^ (-1 / 3 : ℝ)) ℓ t hsub
      (fun j hj y hy => ((hBstep j hj).2 y hy).le) hi hx
    have hsum : ∑ j ∈ Finset.range i, ((B j).card : ℝ) ^ (-1 / 3 : ℝ) ≤ η := by
      have hisucc : i - 1 + 1 = i := by omega
      have hs := vortex_accumulated_error he he1 (show (0 : ℝ) < m by exact_mod_cast hmpos)
        (fun j => (floorOrbit ε (Fintype.card V) j : ℝ)) (i - 1)
        (by
          intro j hj
          have hh := hlbefore j (by omega)
          exact_mod_cast (show 0 < floorOrbit ε (Fintype.card V) j by omega))
        (fun j _ => floorOrbit_shrinks he.le _ j)
        (by exact_mod_cast hlbefore (i - 1) (by omega))
      rw [hisucc] at hs
      have heq : (∑ j ∈ Finset.range i, ((B j).card : ℝ) ^ (-1 / 3 : ℝ)) =
          ∑ j ∈ Finset.range i, (floorOrbit ε (Fintype.card V) j : ℝ) ^ (-1 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcard j (by have := Finset.mem_range.mp hj; omega)]
      rw [heq]
      exact hs.trans hbudget'
    have hnorm := htel.trans hsum
    rw [hB0, Finset.inter_univ, Finset.card_univ,
      SimpleGraph.card_neighborFinset_eq_degree, hreg x] at hnorm
    have hpos : (0 : ℝ) < (B i).card := by
      have hh : ε * m / 2 ≤ ((B i).card : ℝ) := by rw [hcard i hi]; exact hllower i hi
      linarith
    have heq : (((G.neighborFinset x ∩ B i).card : ℝ) -
        ((D : ℝ) / Fintype.card V) * (B i).card) / (B i).card =
        ((G.neighborFinset x ∩ B i).card : ℝ) / (B i).card - (D : ℝ) / Fintype.card V := by
      field_simp
    rw [← heq, abs_div, abs_of_pos hpos] at hnorm
    exact (div_le_iff₀ hpos).mp hnorm
  have hbase:∀i≤ℓ,0 < i →∀x∈B (i-2),
      |((G.neighborFinset x∩B i).card:ℝ)-((D:ℝ)/Fintype.card V)*(B i).card|≤η*(B i).card:=by
    intro i hi hipos x hx
    exact hstrong i hi hipos x (finset_chain_subset B ℓ hsub (by omega:i-(t+1) ≤ i-2) (by omega) hx)
  exact ⟨⟨⟨ℓ,hlpos,B,hB0,hcard,hsub,hterminalLower,hterminalUpper,hbase⟩,hstrong⟩⟩
end Oberwolfach
