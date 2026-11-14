module

public import Oberwolfach.RootedInducedDensity
public import Oberwolfach.EdgeRetentionDensity
public import Oberwolfach.ProductFailureBounds
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Sampling a fixed number of vertices and independently retaining the
original physical edges. The failure estimate is conditional on fixed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def sampledInducedGraph {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (z : FixedSubset V m × (Sym2 V → Bool)) : SimpleGraph V :=
  spanningRestriction (retainedGraph G z.2) z.1.val

def sampledInducedDense {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (G : SimpleGraph V) (δ α : ℝ) (z : FixedSubset V m × (Sym2 V → Bool)) : Prop :=
  ∀ v∈z.1.val,(δ+α/4)*m<(retainedNeighbourCount G z.1.val z.2 v:ℝ)

theorem sampled_induced_dense_failure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) (m : ℕ) (hm : m≤Fintype.card V)
    (hTm : T.card+1<m) [Nonempty (FixedSubset V m)]
    (μ : Sym2 V → FiniteLaw Bool) (δ α : ℝ) (hα : 0<α)
    (hdeg : ∀ v,(δ+α)*Fintype.card V≤(G.degree v:ℝ))
    (hroots : (T.card:ℝ)+1≤α*m/4)
    (hμ : ∀ e,1-α/8≤(μ e).mass true) :
    ((FiniteLaw.uniform (FixedSubset V m)).prod (FiniteLaw.pi μ)).probability
      (fun z => T⊆z.1.val ∧ ¬sampledInducedDense G δ α z)≤
      4*m*Real.exp (-α^2*m/32)*
        (FiniteLaw.uniform (FixedSubset V m)).probability (fun S => T⊆S.val) := by
  let ρ := FiniteLaw.uniform (FixedSubset V m)
  let A (S : FixedSubset V m) := ∃ v∈S.val,
    ((G.neighborFinset v∩S.val).card:ℝ)≤(δ+α/2)*m
  let B (S : FixedSubset V m) (σ : Sym2 V → Bool) := ∃ v∈S.val,
    (retainedNeighbourCount G S.val σ v:ℝ)≤(δ+α/4)*m
  let c := 2*m*Real.exp (-α^2*m/32)
  have hc : 0≤c := by dsimp [c];positivity
  have hA : ρ.probability (fun S => T⊆S.val ∧ A S)≤
      c*ρ.probability (fun S => T⊆S.val) := by
    have hh := fixedSubset_dense_neighbourhoods T m hm hTm (fun v => G.neighborFinset v)
      δ α hα (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg) hroots
    have hcoef : (2*Real.exp (-α^2*m/8))*(m:ℝ)≤c := by
      dsimp [c]
      have he : Real.exp (-α^2*m/8)≤Real.exp (-α^2*m/32) := by
        apply Real.exp_le_exp.mpr
        have hn : 0≤α^2*(m:ℝ) := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) m)]
    exact hh.trans (mul_le_mul_of_nonneg_right hcoef (finiteLaw_probability_nonneg _ _))
  have hB (S : FixedSubset V m) (hS : ¬A S) : (FiniteLaw.pi μ).probability (B S)≤c := by
    have hraw (v : V) (hv : v∈S.val) : (δ+α/2)*S.val.card≤((G.neighborFinset v∩S.val).card:ℝ) := by
      rw [S.property]
      exact (not_le.mp (fun hh => hS ⟨v,hv,hh⟩)).le
    have hh := retained_induced_min_degree_failure G S.val μ δ α hα
      (by rw [S.property];omega) hμ hraw
    simpa only [S.property,B,c] using hh
  have hh := finiteLaw_product_rooted_failure ρ (FiniteLaw.pi μ)
    (fun S => T⊆S.val) A B c c hc hA hB
  have he : (fun z : FixedSubset V m × (Sym2 V → Bool) => T⊆z.1.val ∧ ¬sampledInducedDense G δ α z)=
      (fun z => T⊆z.1.val ∧ B z.1 z.2) := by
    funext z
    apply propext
    simp only [sampledInducedDense,B,not_forall,not_lt]
    simp
  rw [he]
  convert hh using 1
  dsimp [c]
  ring

end Oberwolfach
