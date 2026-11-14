module

public import Oberwolfach.NearOptimalHypergraphColouring

@[expose] public section

/-! Near-optimal edge colouring, proved from the finite colouring iteration.
The index type may contain repeated edges; only the stated codegree bound
controls their multiplicity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem near_optimal_hypergraph_edge_colouring
    (k : ℕ) (hk : 0<k) (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1/2)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ D₀ : ℕ, 1≤D₀ ∧ ∀ D B : ℕ, D₀≤D → (B : ℝ)≤(D : ℝ)^(1-δ) →
      ∀ (V E : Type) [Fintype V] [Fintype E],
      ∀ (R : E → Finset V),
      (∀ e,(R e).card=k) →
      (∀ v,(hypergraphVertexClique R v).card≤D) →
      (∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B) →
      ∃ f : E → Fin ⌈(1+ε)*(D : ℝ)⌉₊,
        ∀ e g,(hypergraphLineGraph R).Adj e g → f e≠f g := by
  classical
  obtain ⟨N,hN⟩ := near_optimal_hypergraph_list_colouring k hk ε δ hε (by linarith) hδ hδ1
  refine ⟨max 2 N,by omega,?_⟩
  intro D B hD hB V E _ _ R hsize hdegree hcodegree
  have hD2 : 2≤D := (le_max_left _ _).trans hD
  have hDpos : (0 : ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hprod : 0≤(1+ε)*(D : ℝ) := by positivity
  have hcols : ⌈(1+ε)*(D : ℝ)⌉₊≤2*D := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith
  obtain ⟨f,_hf,hproper⟩ := hN D B ((le_max_right _ _).trans hD) hB V E
    (Fin ⌈(1+ε)*(D : ℝ)⌉₊) (by simpa using hcols) R (fun _=>Finset.univ)
    ⌈(1+ε)*(D : ℝ)⌉₊ hsize (by intro e;simp) hdegree hcodegree
    (Nat.le_ceil _) hcols
  exact ⟨f,hproper⟩

end Oberwolfach
