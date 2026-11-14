module

public import Oberwolfach.BipartiteEdgeColouring

@[expose] public section

/-!
Prescribed degrees in finite bipartite multigraphs. Edges have their own
finite type, so parallel copies remain distinct. The integral existence
argument below reduces the cut inequalities to Hall's theorem.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Hall's theorem with integer quotas. Every object is assigned exactly
once, to an eligible index, and each index receives its prescribed quota. -/
theorem quotaAssignment
    {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I]
    (f : I → ℕ) (R : I → E → Prop)
    (htotal : ∑ i, f i = Fintype.card E)
    (hcut : ∀ S : Finset I, ∑ i ∈ S, f i ≤
      (Finset.univ.filter (fun e => ∃ i ∈ S, R i e)).card) :
    ∃ a : E → I, (∀ e, R (a e) e) ∧
      ∀ i, (Finset.univ.filter (fun e => a e = i)).card = f i := by
  classical
  let L := Σ i, Fin (f i)
  let N (u : L) := Finset.univ.filter (R u.1)
  have hHall (A : Finset L) : A.card ≤ (A.biUnion N).card := by
    let S := A.image Sigma.fst
    have hA : A ⊆ S.sigma (fun i => Finset.univ (α := Fin (f i))) := by
      intro u hu
      exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨u, hu, rfl⟩,
        Finset.mem_univ _⟩
    have hN : A.biUnion N =
        Finset.univ.filter (fun e => ∃ i ∈ S, R i e) := by
      ext e
      simp only [Finset.mem_biUnion, N, Finset.mem_filter, Finset.mem_univ,
        true_and, S, Finset.mem_image]
      constructor
      · rintro ⟨u, hu, hr⟩
        exact ⟨u.1, ⟨u, hu, rfl⟩, hr⟩
      · rintro ⟨i, ⟨u, hu, rfl⟩, hr⟩
        exact ⟨u, hu, hr⟩
    calc
      A.card ≤ (S.sigma (fun i => Finset.univ (α := Fin (f i)))).card :=
        Finset.card_le_card hA
      _ = ∑ i ∈ S, f i := by simp [Finset.card_sigma]
      _ ≤ _ := by rw [hN]; exact hcut S
  obtain ⟨g, hg, hR⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  have hcard : Fintype.card L = Fintype.card E := by
    simpa [L, Fintype.card_sigma] using htotal
  let σ : L ≃ E := Equiv.ofBijective g
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩)
  let a (e : E) : I := (σ.symm e).1
  refine ⟨a, ?_, ?_⟩
  · intro e
    have h := (Finset.mem_filter.mp (hR (σ.symm e))).2
    change R (σ.symm e).1 (σ (σ.symm e)) at h
    simpa [a] using h
  · intro i
    rw [Finset.card_filter, ← σ.sum_comp]
    simp only [a, Equiv.symm_apply_apply]
    change (∑ u : (Σ j, Fin (f j)), if u.1 = i then 1 else 0) = f i
    rw [Fintype.sum_sigma]
    have hf (j : I) : (∑ _ : Fin (f j), if j = i then 1 else 0) =
        if j = i then f j else 0 := by
      by_cases h : j = i <;> simp [h]
    simp_rw [hf]
    simp

/-- Integral prescribed degrees, in the cut formulation
`f(S) ≤ g(T) + e(S,Y \ T)`. The selected object is a subset of the
original edge type, so each edge can be used at most once. -/
theorem bipartite_prescribedDegrees
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    (htotal : ∑ x, f x = ∑ y, g y)
    (hcut : ∀ (S : Finset X) (T : Finset Y),
      ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
        (Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∉ T)).card) :
    ∃ H : Finset E,
      (∀ x, (H.filter (fun e => tail e = x)).card = f x) ∧
      (∀ y, (H.filter (fun e => head e = y)).card = g y) := by
  classical
  let deg (y : Y) := (Finset.univ.filter (fun e => head e = y)).card
  have hg (y : Y) : g y ≤ deg y := by
    have hc := hcut Finset.univ (Finset.univ.erase y)
    have hs := Finset.sum_erase_add Finset.univ g (Finset.mem_univ y)
    have he : (Finset.univ.filter
        (fun e => tail e ∈ Finset.univ ∧ head e ∉ Finset.univ.erase y)).card =
        deg y := by simp [deg]
    rw [he, htotal] at hc
    omega
  have hdeg (T : Finset Y) : ∑ y ∈ T, deg y =
      (Finset.univ.filter (fun e => head e ∈ T)).card :=
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ T head
  have hdegTotal : ∑ y, deg y = Fintype.card E := by
    simpa using hdeg Finset.univ
  let d : X ⊕ Y → ℕ := Sum.elim f (fun y => deg y - g y)
  let R : X ⊕ Y → E → Prop := Sum.elim (fun x e => tail e = x)
    (fun y e => head e = y)
  have hdtotal : ∑ i, d i = Fintype.card E := by
    simp only [d, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_tsub_distrib _ (fun y _ => hg y), htotal, hdegTotal]
    have hs : ∑ y, g y ≤ Fintype.card E := by
      rw [← hdegTotal]; exact Finset.sum_le_sum (fun y _ => hg y)
    omega
  have hdcut (A : Finset (X ⊕ Y)) : ∑ i ∈ A, d i ≤
      (Finset.univ.filter (fun e => ∃ i ∈ A, R i e)).card := by
    let S := A.toLeft
    let T := A.toRight
    have hR (e : E) : (∃ i ∈ A, R i e) ↔ tail e ∈ S ∨ head e ∈ T := by
      constructor
      · rintro ⟨i, hi, hr⟩
        cases i with
        | inl x =>
          change tail e = x at hr
          exact Or.inl (hr ▸ (Finset.mem_toLeft.mpr hi))
        | inr y =>
          change head e = y at hr
          exact Or.inr (hr ▸ (Finset.mem_toRight.mpr hi))
      · intro h
        rcases h with h | h
        · exact ⟨.inl (tail e), Finset.mem_toLeft.mp h, rfl⟩
        · exact ⟨.inr (head e), Finset.mem_toRight.mp h, rfl⟩
    have hN : (Finset.univ.filter (fun e => ∃ i ∈ A, R i e)).card =
        (Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∉ T)).card +
          ∑ y ∈ T, deg y := by
      simp_rw [hR]
      rw [hdeg, Finset.card_filter, Finset.card_filter, Finset.card_filter,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases ht : head e ∈ T <;> by_cases hs : tail e ∈ S <;> simp [ht, hs]
    have hs : ∑ i ∈ A, d i =
        (∑ x ∈ S, f x) + (∑ y ∈ T, (deg y - g y)) := by
      rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
      rfl
    have ht : ∑ y ∈ T, g y ≤ ∑ y ∈ T, deg y :=
      Finset.sum_le_sum (fun y _ => hg y)
    rw [hN, hs, Finset.sum_tsub_distrib _ (fun y _ => hg y)]
    have hc := hcut S T
    omega
  obtain ⟨a, ha, hquota⟩ := quotaAssignment d R hdtotal hdcut
  let H := Finset.univ.filter (fun e => (a e).isLeft)
  have hx (x : X) : H.filter (fun e => tail e = x) =
      Finset.univ.filter (fun e => a e = .inl x) := by
    ext e
    have he := ha e
    cases h : a e with
    | inl z =>
      have ht : tail e = z := by simpa [R, h] using he
      simp [H, h, ht]
    | inr z => simp [H, h]
  have hy (y : Y) : (Finset.univ.filter (fun e => head e = y)).filter
      (fun e => ¬(a e).isLeft) = Finset.univ.filter (fun e => a e = .inr y) := by
    ext e
    have he := ha e
    cases h : a e with
    | inl z => simp [h]
    | inr z =>
      have ht : head e = z := by simpa [R, h] using he
      simp [h, ht]
  refine ⟨H, ?_, ?_⟩
  · intro x
    rw [hx]
    exact hquota (.inl x)
  · intro y
    have hc := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun e => head e = y)) (fun e => (a e).isLeft)
    have hswap : (Finset.univ.filter (fun e => head e = y)).filter
        (fun e => (a e).isLeft) = H.filter (fun e => head e = y) := by
      ext e
      simp [H, and_comm]
    have hqy : (Finset.univ.filter (fun e => a e = .inr y)).card =
        deg y - g y := by
      exact hquota (.inr y)
    rw [hswap, hy, hqy] at hc
    change (H.filter (fun e => head e = y)).card + (deg y - g y) = deg y at hc
    have := hg y
    omega

/-- Counting a specified set of endpoint pairs counts every parallel copy. -/
theorem bipartiteEdges_filter_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → ℕ) (p : X → Y → Prop) [DecidableRel p] :
    (Finset.univ.filter (fun e : BipartiteEdges M => p e.1 e.2.1)).card =
      ∑ x, ∑ y, if p x y then M x y else 0 := by
  classical
  rw [Finset.card_filter]
  change (∑ e : (Σ x, Σ y, Fin (M x y)), if p e.1 e.2.1 then 1 else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hp : p x y <;> simp [hp]

/-- Matrix form of integral prescribed degrees. The capacity `M x y`
is the number of distinct available edges between the endpoints. -/
theorem bipartite_prescribedMultiplicity
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (M : X → Y → ℕ) (f : X → ℕ) (g : Y → ℕ)
    (htotal : ∑ x, f x = ∑ y, g y)
    (hcut : ∀ (S : Finset X) (T : Finset Y),
      ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
        ∑ x, ∑ y, if x ∈ S ∧ y ∉ T then M x y else 0) :
    ∃ Q : X → Y → ℕ,
      (∀ x y, Q x y ≤ M x y) ∧
      (∀ x, ∑ y, Q x y = f x) ∧
      (∀ y, ∑ x, Q x y = g y) := by
  classical
  obtain ⟨H, hHrow, hHcol⟩ := bipartite_prescribedDegrees
    (fun e : BipartiteEdges M => e.1) (fun e => e.2.1) f g htotal
    (fun S T => by
      rw [bipartiteEdges_filter_card M (fun x y => x ∈ S ∧ y ∉ T)]
      exact hcut S T)
  let Q (x : X) (y : Y) :=
    (H.filter (fun e => e.1 = x ∧ e.2.1 = y)).card
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro x y
    calc
      Q x y ≤ (Finset.univ.filter
          (fun e : BipartiteEdges M => e.1 = x ∧ e.2.1 = y)).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ (Finset.subset_univ H)
      _ = M x y := by
        rw [bipartiteEdges_filter_card M (fun z w => z = x ∧ w = y)]
        simp only [ite_and]
        simp
  · intro x
    have hc := Finset.sum_card_fiberwise_eq_card_filter
      (H.filter (fun e => e.1 = x)) Finset.univ (fun e => e.2.1)
    simpa [Q, Finset.filter_filter, hHrow x] using hc
  · intro y
    have hc := Finset.sum_card_fiberwise_eq_card_filter
      (H.filter (fun e => e.2.1 = y)) Finset.univ (fun e => e.1)
    simpa [Q, Finset.filter_filter, and_comm, hHcol y] using hc

end Oberwolfach
