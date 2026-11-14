module

public import Oberwolfach.DegreeCutHall

@[expose] public section

/-! Hall's condition for the three blocks XK--Y0, X0--Y0 and X0--YK.
The surplus of Y0 over XK prevents a deficient set concentrated in XK. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem three_block_perfect_matching {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X → Y → Prop) (P : X → Prop) (Q : Y → Prop)
    (hcard : Fintype.card X = Fintype.card Y)
    (a : ℝ) (ha : 0 < a)
    (hrow : ∀ x, 2*a ≤ ((Finset.univ.filter (E x)).card : ℝ))
    (hcol : ∀ y, 2*a ≤ ((Finset.univ.filter (fun x => E x y)).card : ℝ))
    (hgap : ((Finset.univ.filter P).card : ℝ) + 2*a ≤
      (Finset.univ.filter (fun y => ¬Q y)).card)
    (hcut : ∀ S : Finset X, ∀ T : Finset Y,
      a ≤ (S.card : ℝ) → a ≤ (T.card : ℝ) →
      ((∀ x∈S, ¬P x) ∧ ((∀ y∈T, Q y) ∨ (∀ y∈T, ¬Q y)) ∨
       (∀ x∈S, P x) ∧ (∀ y∈T, ¬Q y)) →
      ∃ x∈S, ∃ y∈T, E x y) :
    ∃ σ : X ≃ Y, ∀ x, E x (σ x) := by
  classical
  have hhall (S : Finset X) :
      S.card ≤ (S.biUnion (fun x => Finset.univ.filter (E x))).card := by
    let N := S.biUnion (fun x => Finset.univ.filter (E x))
    let T := Finset.univ \ N
    by_contra hf
    have hlt : N.card < S.card := lt_of_not_ge hf
    obtain ⟨x,hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hrsub : Finset.univ.filter (E x) ⊆ N :=
      fun y hy => Finset.mem_biUnion.mpr ⟨x,hx,hy⟩
    have hSlarge : 2*a < (S.card : ℝ) :=
      (hrow x).trans_lt ((Nat.cast_le.mpr (Finset.card_le_card hrsub)).trans_lt
        (Nat.cast_lt.mpr hlt))
    have hNcard : N.card ≤ Fintype.card Y := Finset.card_le_univ _
    have hTcard : T.card + N.card = Fintype.card Y := by
      dsimp [T]; rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      omega
    obtain ⟨y,hy⟩ : T.Nonempty := Finset.card_pos.mp (by
      have := Finset.card_le_univ S
      omega)
    have hzero : ∀ x∈S, ∀ y∈T, ¬E x y := by
      intro x hx y hy he
      exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩)
    have hcsub : Finset.univ.filter (fun x => E x y) ⊆ Finset.univ \ S := by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hzS =>
        hzero z hzS y hy (Finset.mem_filter.mp hz).2⟩
    have hccomp : (Finset.univ \ S).card < T.card := by
      have hScard := Finset.card_le_univ S
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
      omega
    have hTlarge : 2*a < (T.card : ℝ) :=
      (hcol y).trans_lt ((Nat.cast_le.mpr (Finset.card_le_card hcsub)).trans_lt
        (Nat.cast_lt.mpr hccomp))
    have hSp : ((S.filter P).card : ℝ) + (S.filter (fun x => ¬P x)).card = S.card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s:=S) P
    have hTp : ((T.filter Q).card : ℝ) + (T.filter (fun y => ¬Q y)).card = T.card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s:=T) Q
    have hno (S' : Finset X) (T' : Finset Y) (hs : S'⊆S) (ht : T'⊆T)
        (hs' : a ≤ (S'.card : ℝ)) (ht' : a ≤ (T'.card : ℝ))
        (hp : ((∀ x∈S', ¬P x) ∧ ((∀ y∈T', Q y) ∨ (∀ y∈T', ¬Q y)) ∨
          (∀ x∈S', P x) ∧ (∀ y∈T', ¬Q y))) : False := by
      obtain ⟨v,hv,w,hw,he⟩ := hcut S' T' hs' ht' hp
      exact hzero v (hs hv) w (ht hw) he
    by_cases hs0 : a ≤ ((S.filter (fun x => ¬P x)).card : ℝ)
    · have htK : ((T.filter Q).card : ℝ) < a := by
        by_contra ht; apply hno _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hs0 (le_of_not_gt ht)
        exact Or.inl ⟨fun _ h => (Finset.mem_filter.mp h).2,Or.inl (fun _ h => (Finset.mem_filter.mp h).2)⟩
      have ht0 : ((T.filter (fun y => ¬Q y)).card : ℝ) < a := by
        by_contra ht; apply hno _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hs0 (le_of_not_gt ht)
        exact Or.inl ⟨fun _ h => (Finset.mem_filter.mp h).2,Or.inr (fun _ h => (Finset.mem_filter.mp h).2)⟩
      linarith
    · have hsK : a ≤ ((S.filter P).card : ℝ) := by linarith
      have ht0 : ((T.filter (fun y => ¬Q y)).card : ℝ) < a := by
        by_contra ht; apply hno _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hsK (le_of_not_gt ht)
        exact Or.inr ⟨fun _ h => (Finset.mem_filter.mp h).2,fun _ h => (Finset.mem_filter.mp h).2⟩
      have hsKbound : ((S.filter P).card : ℝ) ≤ (Finset.univ.filter P).card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter P (Finset.subset_univ S))
      have hcover : Finset.univ.filter (fun y => ¬Q y) ⊆ N ∪ T.filter (fun y => ¬Q y) := by
        intro z hz
        by_cases hn : z∈N
        · exact Finset.mem_union_left _ hn
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩,(Finset.mem_filter.mp hz).2⟩)
      have hy0 : ((Finset.univ.filter (fun y => ¬Q y)).card : ℝ) ≤
          N.card + (T.filter (fun y => ¬Q y)).card := by
        exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
      have hltR : (N.card : ℝ) < S.card := Nat.cast_lt.mpr hlt
      linarith
  obtain ⟨f,hf,hE⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun x => Finset.univ.filter (E x))).mp hhall
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),
    fun x => (Finset.mem_filter.mp (hE x)).2⟩

end Oberwolfach
