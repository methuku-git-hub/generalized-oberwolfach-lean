module

public import Oberwolfach.LocalExtensionCounts
public import Oberwolfach.PermutationConflictDegree

@[expose] public section

/-! The ordinary local-extension lemma. Both positive coefficients and
the tolerance precede the conflict radius. Only the order threshold
depends on that radius, and neighbourhood hypotheses include every root
in the ambient vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_extensions (r : ℕ) (hr : 3≤r) (α ρ₀ s₀ : ℝ)
    (hα : 0<α) (hρ₀ : 0<ρ₀) (hρ₀1 : ρ₀≤1) (hs₀ : 0<s₀) (hs₀1 : s₀≤1) :
    ∃ β ε₀ : ℝ,0<β ∧ 0<ε₀ ∧ ∀ d : ℕ,∃ N : ℕ,
      ∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P R : SimpleGraph V) (H : V→U→Prop) (π : Equiv.Perm V)
        (A : Finset V) (B : Finset U) (ρ s ε : ℝ),N≤A.card →
      ρ₀≤ρ → s₀≤s → ε≤ε₀ →
      (∀ v,(cycleThreshold r+α)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ X : Finset V,∀ J : Finset U,X.card≤ordinaryExtensionRootBound r → J.card≤2 →
        (ρ*s)^X.card*s^J.card*((common A X (fun v=>(P\permutationConflictGraph π (3*d)).neighborFinset v)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun v=>R.neighborFinset v)) J
            (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)) →
      (∀ X : Finset V,X.card≤r+6 →
        (∀ v∈X,∀ w∈X,¬(permutationConflictGraph π (3*d)).Adj v w) →
        (s^X.card-ε)*B.card≤((common B X (fun v=>Finset.univ.filter (H v))).card:ℝ)) →
      (∀ X : Finset V,∀ J : Finset U,X.card≤ordinaryExtensionRootBound r → J.card≤2 →
        β*A.card≤((common (common A X (fun v=>R.neighborFinset v)) J
          (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)) ∧
      (∀ X : Finset V,X.card≤r+6 → (X:Set V).Pairwise (fun v w=>¬PermutationClose π (3*d) v w) →
        β*B.card≤((common B X (fun v=>Finset.univ.filter (H v))).card:ℝ)) := by
  let γ:=min α 1
  let p:=ρ₀*s₀
  let β:=min (p^6*γ/4) (s₀^(r+6)/2)
  have hγ : 0<γ := lt_min hα (by norm_num)
  have hγ1 : γ≤1 := min_le_right _ _
  have hγα : γ≤α := min_le_left _ _
  have hp : 0<p := mul_pos hρ₀ hs₀
  have hps : p≤s₀ := by dsimp [p];nlinarith only [hρ₀1,hs₀.le]
  have hp1 : p≤1 := hps.trans hs₀1
  have hβ : 0<β := by dsimp [β];positivity
  refine ⟨β,β,hβ,hβ,?_⟩
  intro d
  obtain ⟨N,hN⟩:=exists_nat_gt ((48:ℝ)*d/γ)
  refine ⟨N,?_⟩
  intro V U _ _ _ _ P R H π A B ρ s ε hn hρ hs hε hdeg hrows hindices
  let k:=ordinaryExtensionRootBound r
  have hk:=ordinaryExtensionRootBound_range r
  have hAn : (N:ℝ)≤A.card := by exact_mod_cast hn
  have hscale : (48:ℝ)*d≤γ*A.card := by
    have hh:=(div_lt_iff₀ hγ).mp (hN.trans_le hAn)
    nlinarith only [hh]
  have hkR : (k:ℝ)≤4 := by exact_mod_cast hk.2
  have hloss : (k:ℝ)*(6*d)≤γ*A.card/2 := by
    have hh:=mul_le_mul_of_nonneg_right hkR (by positivity : (0:ℝ)≤6*d)
    nlinarith only [hh,hscale]
  have hF (v : V) : ((permutationConflictGraph π (3*d)).degree v:ℝ)≤6*d := by
    have hh:=permutationConflictGraph_degree_le π (3*d) v
    exact_mod_cast (by omega : (permutationConflictGraph π (3*d)).degree v≤6*d)
  have hq : p≤ρ*s := mul_le_mul hρ hs hs₀.le (hρ₀.le.trans hρ)
  have hdeg' (v : V) : (1-1/(k:ℝ)+γ)*A.card≤((A∩P.neighborFinset v).card:ℝ) := by
    have hh:=ordinaryExtensionRootBound_threshold r hr
    exact (mul_le_mul_of_nonneg_right (by dsimp [k];linarith only [hh,hγα])
      (Nat.cast_nonneg A.card)).trans (hdeg v)
  constructor
  · intro X J hX hJ
    have hc:=extension_relative_row_lower P R (permutationConflictGraph π (3*d)) A X J
      (fun u=>Finset.univ.filter (fun v=>H v u)) k γ p (ρ*s) s ε (6*d)
      hk.1 hk.2 hγ hγ1 hp hp1 hq (hps.trans hs) (by positivity) hX hJ hloss
      (hε.trans (min_le_left _ _)) (fun v _=>hdeg' v) (fun v _=>hF v)
      (by convert hrows X J hX hJ using 1 <;> congr!)
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg A.card)).trans hc
  · intro X hX hsep
    have hind : ∀ v∈X,∀ w∈X,¬(permutationConflictGraph π (3*d)).Adj v w := by
      intro v hv w hw he
      exact hsep hv hw he.1 he.2
    have hc:=extension_relative_index_lower B X (fun v=>Finset.univ.filter (H v)) r s₀ s ε
      hs₀ hs₀1 hs hX (hε.trans (min_le_right _ _)) (hindices X hX hind)
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg B.card)).trans hc

end Oberwolfach
