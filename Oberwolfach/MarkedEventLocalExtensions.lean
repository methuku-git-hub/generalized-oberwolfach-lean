module

public import Oberwolfach.MarkedRowExtensionApplication
public import Oberwolfach.MarkedIndexExtensionApplication

@[expose] public section

/-! One common realized row/index estimate supplies all four marked
extension sets and all later separated index requests on the fixed domains.
The coefficient and tolerance precede d and the supplied marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_event_local_extensions (c : ℕ) (α pstar : ℝ)
    (hα : 0<α) (hpstar : 0<pstar) (hpstar1 : pstar≤1) :
    ∃ β ε₀ : ℝ,0<β ∧ 0<ε₀ ∧ ∀ d : ℕ,∃ N : ℕ,
      ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
      ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (A : Finset V) (B : Finset U)
        (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε : ℝ),
      N≤A.card → A.image π=A → ε≤ε₀ → pstar≤p → pstar≤k →
      (∀ u,pstar≤q u g) → (∀ u,pstar≤s u j) →
      (∀ v,(1/2+α)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      ∀ (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop),
      MarkedRowsWithSpokes P π d (c+6) A p k q s g j (ε*A.card) σ H →
      MarkedIndicesWithSpokes π d (c+6) B q s g j (ε*B.card) σ H →
      (∀ b v u,β*A.card≤((markedOneExtensionSet (rawMarkedPairRims P π d σ) H A b v u).card:ℝ)) ∧
      (∀ b v w u,v≠(if b then π w else w) →
        β*A.card≤((markedTwoExtensionSet (rawMarkedPairRims P π d σ) H A b v w u).card:ℝ)) ∧
      (∀ X Y : Finset V,Disjoint X Y → (X∪Y).card≤c+6 →
        ((X∪Y):Set V).Pairwise (fun v w=>¬PermutationClose π (3*d) v w) →
        β*B.card≤((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
          (fun v=>Finset.univ.filter (H true v))).card:ℝ)) := by
  let γ:=min α 1
  let β:=min (pstar^3*γ/4) (pstar^(c+6)/2)
  have hγ : 0<γ := lt_min hα (by norm_num)
  have hγ1 : γ≤1 := min_le_right _ _
  have hγα : γ≤α := min_le_left _ _
  have hβ : 0<β := by dsimp [β];positivity
  refine ⟨β,β,hβ,hβ,?_⟩
  intro d
  obtain ⟨N,hN⟩:=exists_nat_gt (4*(6*(d:ℝ)+1)/γ)
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P π A B p k q s g j ε hn hA hε hp hk hq hs hdeg σ H hrows hindices
  have hAn : (N:ℝ)≤A.card := by exact_mod_cast hn
  have hloss : 2*(2*(3*d:ℕ)+1:ℝ)≤γ*A.card/2 := by
    have hh:=(div_lt_iff₀ hγ).mp (hN.trans_le hAn)
    push_cast
    nlinarith only [hh]
  have hdeg' (v : V) : (1/2+γ/2)*A.card≤((A∩P.neighborFinset v).card:ℝ) := by
    exact (mul_le_mul_of_nonneg_right (by linarith only [hγα,hγ]) (Nat.cast_nonneg A.card)).trans (hdeg v)
  obtain ⟨h₁,h₂⟩:=marked_row_event_extension_sets P π d (c+6) (by omega) A hA p k q s g j γ pstar ε
    hγ hγ1 hpstar hpstar1 hp hk hq hs hloss (hε.trans (min_le_left _ _)) hdeg' σ H hrows
  refine ⟨?_,?_,?_⟩
  · intro b v u
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg A.card)).trans (h₁ b v u)
  · intro b v w u hne
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg A.card)).trans (h₂ b v w u hne)
  · intro X Y hXY hsize hsep
    have hh:=marked_index_event_extension_lower π d (c+6) B q s g j pstar ε hpstar hpstar1
      (fun u _=>hq u) (fun u _=>hs u) (hε.trans (min_le_right _ _)) σ H hindices X Y hXY hsize hsep
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg B.card)).trans hh

end Oberwolfach
