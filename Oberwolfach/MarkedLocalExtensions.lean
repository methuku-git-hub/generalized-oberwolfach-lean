module

public import Oberwolfach.MarkedExtensionLowerBounds

@[expose] public section

/-! The marked local-extension conclusion from precisely the four row
patterns and the separated index patterns. Constants precede d and the
actual density profile. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_local_extensions (c : ℕ) (α pstar : ℝ)
    (hα : 0<α) (hpstar : 0<pstar) (hpstar1 : pstar≤1) :
    ∃ β ε₀ : ℝ,0<β ∧ 0<ε₀ ∧ ∀ d : ℕ,∃ N : ℕ,
      ∀ (V U : Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
      ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (R : (V×V)⊕(V×V)→Prop)
        (H : Bool→V→U→Prop) (A : Finset V) (B : Finset U)
        (p s : Bool→ℝ) (ε : ℝ),N≤A.card → A.image π=A → ε≤ε₀ →
      (∀ j,pstar≤p j) → (∀ j,pstar≤s j) →
      (∀ v,(1/2+α)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ j v u,p j*s j*(markedRowDomain P π (3*d) A (markedOneExtensionRequests j v) ∅).card-ε*A.card≤
        markedRelationRowCount R H (markedRowDomain P π (3*d) A (markedOneExtensionRequests j v) ∅)
          (markedOneExtensionRequests j v) {(j,u)}) →
      (∀ j v w u,v≠(if j then π w else w) →
        p false*p j*s false*(markedRowDomain P π (3*d) A (markedTwoExtensionRequests j v w) ∅).card-ε*A.card≤
        markedRelationRowCount R H (markedRowDomain P π (3*d) A (markedTwoExtensionRequests j v w) ∅)
          (markedTwoExtensionRequests j v w) {(false,u)}) →
      (∀ X Y : Finset V,Disjoint X Y → (X∪Y).card≤c+6 →
        ((X∪Y):Set V).Pairwise (fun v w=>¬PermutationClose π (3*d) v w) →
        ((s false)^X.card*(s true)^Y.card-ε)*B.card≤
          ((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
            (fun v=>Finset.univ.filter (H true v))).card:ℝ)) →
      (∀ j v u,β*A.card≤((markedOneExtensionSet R H A j v u).card:ℝ)) ∧
      (∀ j v w u,v≠(if j then π w else w) →
        β*A.card≤((markedTwoExtensionSet R H A j v w u).card:ℝ)) ∧
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
  intro V U _ _ _ _ P π R H A B p s ε hn hA hε hp hs hdeg hrows₁ hrows₂ hindices
  have hAn : (N:ℝ)≤A.card := by exact_mod_cast hn
  have hloss : 2*(2*(3*d:ℕ)+1:ℝ)≤γ*A.card/2 := by
    have hh:=(div_lt_iff₀ hγ).mp (hN.trans_le hAn)
    push_cast
    nlinarith only [hh]
  have hdeg' (v : V) : (1/2+γ/2)*A.card≤((A∩P.neighborFinset v).card:ℝ) := by
    exact (mul_le_mul_of_nonneg_right (by linarith only [hγα,hγ]) (Nat.cast_nonneg A.card)).trans (hdeg v)
  refine ⟨?_,?_,?_⟩
  · intro j v u
    have hh:=marked_one_extension_lower P π (3*d) R H A hA j v u γ pstar (p j) (s j) ε
      hγ hγ1 hpstar hpstar1 (hp j) (hs j) hloss (hε.trans (min_le_left _ _)) hdeg' (hrows₁ j v u)
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg A.card)).trans hh
  · intro j v w u hne
    have hh:=marked_two_extension_lower P π (3*d) R H A j v w u hne γ pstar (p false) (p j) (s false) ε
      hγ hγ1 hpstar (hp false) (hp j) (hs false) hloss (hε.trans (min_le_left _ _)) hdeg' (hrows₂ j v w u hne)
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg A.card)).trans hh
  · intro X Y hXY hsize hsep
    have hsum : X.card+Y.card≤c+6 := by rwa [Finset.card_union_of_disjoint hXY] at hsize
    have hh:=marked_extension_index_lower H B X Y c pstar (s false) (s true) ε hpstar hpstar1
      (hs false) (hs true) hsum (hε.trans (min_le_right _ _)) (hindices X Y hXY hsize hsep)
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg B.card)).trans hh

theorem marked_one_extension_physical_edges {V U : Type} [Fintype V] [Fintype U]
    [LinearOrder V] [DecidableEq U] (P : SimpleGraph V) (π : Equiv.Perm V)
    (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (hR₀ : ∀ v w,R (Sum.inl (v,w)) → P.Adj v w)
    (hRₖ : ∀ v w,R (Sum.inr (v,w)) → P.Adj v (π w))
    (A : Finset V) (j : Bool) (v z : V) (u : U)
    (hz : z∈markedOneExtensionSet R H A j v u) :
    P.Adj v (if j then π z else z) ∧ v≠if j then π z else z := by
  have hr:=(Finset.mem_filter.mp hz).2.1
  have he:P.Adj v (if j then π z else z) := by
    cases j
    · exact hR₀ v z hr
    · exact hRₖ v z hr
  exact ⟨he,he.ne⟩

theorem marked_two_extension_physical_edges {V U : Type} [Fintype V] [Fintype U]
    [LinearOrder V] [DecidableEq U] (P : SimpleGraph V) (π : Equiv.Perm V)
    (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (hR₀ : ∀ v w,R (Sum.inl (v,w)) → P.Adj v w)
    (hRₖ : ∀ v w,R (Sum.inr (v,w)) → P.Adj v (π w))
    (A : Finset V) (j : Bool) (v w z : V) (u : U) (hne : v≠if j then π w else w)
    (hz : z∈markedTwoExtensionSet R H A j v w u) :
    P.Adj v z ∧ P.Adj z (if j then π w else w) ∧
      v≠z ∧ z≠(if j then π w else w) ∧ s(v,z)≠s(z,if j then π w else w) := by
  have hr:=(Finset.mem_filter.mp hz).2
  have he₀:=hR₀ v z hr.1
  have he₁:P.Adj z (if j then π w else w) := by
    cases j
    · exact hR₀ z w hr.2.1
    · exact hRₖ z w hr.2.1
  exact ⟨he₀,he₁,he₀.ne,he₁.ne,marked_two_extension_edges_distinct π j v w z hne⟩

end Oberwolfach
