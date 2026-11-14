module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Tactic

@[expose] public section

/-!
Finite bipartite multigraphs represented by their natural-valued edge
multiplicities. This keeps parallel edges: no simple-graph identification is
made. The regular case supplies the perfect matchings used at the end of
`lem:family:partition`.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem regularBipartite_card_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → ℕ) {d : ℕ} (hd : 0 < d)
    (hrow : ∀ x, ∑ y, M x y = d)
    (hcol : ∀ y, ∑ x, M x y = d) :
    Fintype.card X = Fintype.card Y := by
  have h : Fintype.card X * d = Fintype.card Y * d := by
    calc
      _ = ∑ x, ∑ y, M x y := by simp [hrow]
      _ = ∑ y, ∑ x, M x y := Finset.sum_comm
      _ = _ := by simp [hcol]
  exact Nat.eq_of_mul_eq_mul_right hd h

theorem regularBipartite_hall
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : X → Y → ℕ) {d : ℕ} (hd : 0 < d)
    (hrow : ∀ x, ∑ y, M x y = d)
    (hcol : ∀ y, ∑ x, M x y = d) (S : Finset X) :
    S.card ≤ (S.biUnion (fun x => Finset.univ.filter (fun y => 0 < M x y))).card := by
  classical
  let N := S.biUnion (fun x => Finset.univ.filter (fun y => 0 < M x y))
  have hzero (x : X) (hx : x ∈ S) (y : Y) (hy : y ∉ N) : M x y = 0 := by
    by_contra h
    apply hy
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩⟩
  have hleft : ∑ x ∈ S, ∑ y ∈ N, M x y = S.card * d := by
    calc
      _ = ∑ x ∈ S, ∑ y, M x y := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_subset (Finset.subset_univ _) 
        intro y _ hy
        exact hzero x hx y hy
      _ = _ := by simp [hrow]
  have hright : ∑ y ∈ N, ∑ x ∈ S, M x y ≤ N.card * d := by
    calc
      _ ≤ ∑ y ∈ N, ∑ x, M x y := by
        apply Finset.sum_le_sum
        intro y _
        exact Finset.sum_le_univ_sum_of_nonneg (fun x => Nat.zero_le (M x y))
      _ = _ := by simp [hcol]
  rw [Finset.sum_comm, hleft] at hright
  exact Nat.le_of_mul_le_mul_right hright hd

/-- A positive regular bipartite multigraph contains one perfect matching. -/
theorem regularBipartite_perfectMatching
    {X Y : Type*} [Fintype X] [Fintype Y]
    (M : X → Y → ℕ) {d : ℕ} (hd : 0 < d)
    (hrow : ∀ x, ∑ y, M x y = d)
    (hcol : ∀ y, ∑ x, M x y = d) :
    ∃ σ : X ≃ Y, ∀ x, 0 < M x (σ x) := by
  classical
  obtain ⟨f, hf, hpos⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x => Finset.univ.filter (fun y => 0 < M x y))).mp
      (regularBipartite_hall M hd hrow hcol)
  let σ := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, regularBipartite_card_eq M hd hrow hcol⟩)
  exact ⟨σ, fun x => (Finset.mem_filter.mp (hpos x)).2⟩

/-- Decomposition into perfect matchings, with exact edge multiplicities. -/
theorem regularBipartite_decomposition
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (d : ℕ) (M : X → Y → ℕ)
    (hrow : ∀ x, ∑ y, M x y = d)
    (hcol : ∀ y, ∑ x, M x y = d) :
    ∃ σ : Fin d → X ≃ Y,
      ∀ x y, M x y = ∑ c, if σ c x = y then 1 else 0 := by
  classical
  induction d generalizing M with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro x y
    have hle : M x y ≤ ∑ z, M x z :=
      Finset.single_le_sum (fun z _ => Nat.zero_le (M x z)) (Finset.mem_univ y)
    simpa [hrow x] using hle
  | succ d ih =>
    obtain ⟨σ, hσ⟩ := regularBipartite_perfectMatching M (Nat.succ_pos d) hrow hcol
    let I : X → Y → ℕ := fun x y => if σ x = y then 1 else 0
    have hI (x : X) (y : Y) : I x y ≤ M x y := by
      dsimp [I]
      split_ifs with h
      · subst y
        exact hσ x
      · exact Nat.zero_le _
    have hIrow (x : X) : ∑ y, I x y = 1 := by simp [I]
    have hIcol (y : Y) : ∑ x, I x y = 1 := by
      simp only [I, ← Equiv.eq_symm_apply]
      simp
    let N : X → Y → ℕ := fun x y => M x y - I x y
    have hNrow (x : X) : ∑ y, N x y = d := by
      dsimp [N]
      rw [Finset.sum_tsub_distrib _ (fun y _ => hI x y), hrow x, hIrow x]
      omega
    have hNcol (y : Y) : ∑ x, N x y = d := by
      dsimp [N]
      rw [Finset.sum_tsub_distrib _ (fun x _ => hI x y), hcol y, hIcol y]
      omega
    obtain ⟨τ, hτ⟩ := ih N hNrow hNcol
    refine ⟨Fin.cons σ τ, ?_⟩
    intro x y
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hτ x y]
    exact (Nat.add_sub_of_le (hI x y)).symm

/-- Kőnig's theorem for a finite bipartite multigraph. `R c x y` means that
colour `c` contains one of the edges from `x` to `y`. The cardinality identity
retains every parallel edge, and the last two conclusions say each colour is
a matching. -/
theorem bipartiteMultigraph_edgeColouring
    {X Y : Type*} [Fintype X] [Fintype Y]
    (d : ℕ) (M : X → Y → ℕ)
    (hrow : ∀ x, ∑ y, M x y ≤ d)
    (hcol : ∀ y, ∑ x, M x y ≤ d) :
    ∃ R : Fin d → X → Y → Prop,
      (∀ x y, Nat.card {c : Fin d // R c x y} = M x y) ∧
      (∀ c x y z, R c x y → R c x z → y = z) ∧
      (∀ c x z y, R c x y → R c z y → x = z) := by
  classical
  let N : X ⊕ Y → Y ⊕ X → ℕ
    | .inl x, .inl y => M x y
    | .inl x, .inr z => if x = z then d - ∑ y, M x y else 0
    | .inr y, .inl z => if y = z then d - ∑ x, M x y else 0
    | .inr y, .inr x => M x y
  have hNrow : ∀ u, ∑ v, N u v = d := by
    intro u
    cases u with
    | inl x => simp [Fintype.sum_sum_type, N, Nat.add_sub_of_le (hrow x)]
    | inr y => simp [Fintype.sum_sum_type, N, Nat.sub_add_cancel (hcol y)]
  have hNcol : ∀ v, ∑ u, N u v = d := by
    intro v
    cases v with
    | inl y => simp [Fintype.sum_sum_type, N, Nat.add_sub_of_le (hcol y)]
    | inr x => simp [Fintype.sum_sum_type, N, Nat.sub_add_cancel (hrow x)]
  obtain ⟨σ, hσ⟩ := regularBipartite_decomposition d N hNrow hNcol
  refine ⟨fun c x y => σ c (.inl x) = .inl y, ?_, ?_, ?_⟩
  · intro x y
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    exact (hσ (.inl x) (.inl y)).symm
  · intro c x y z hy hz
    exact Sum.inl_injective (hy.symm.trans hz)
  · intro c x z y hx hz
    exact Sum.inl_injective ((σ c).injective (hx.trans hz.symm))

/-- The grouping used in the protected regular partition: a `k*q`-regular
bipartite multigraph splits into `k` multigraphs of degree `q` on both sides. -/
theorem regularBipartite_groupedDecomposition
    {X Y : Type*} [Fintype X] [Fintype Y]
    (k q : ℕ) (M : X → Y → ℕ)
    (hrow : ∀ x, ∑ y, M x y = k * q)
    (hcol : ∀ y, ∑ x, M x y = k * q) :
    ∃ Q : Fin k → X → Y → ℕ,
      (∀ x y, ∑ a, Q a x y = M x y) ∧
      (∀ a x, ∑ y, Q a x y = q) ∧
      (∀ a y, ∑ x, Q a x y = q) := by
  classical
  obtain ⟨σ, hσ⟩ := regularBipartite_decomposition (k * q) M hrow hcol
  let τ (a : Fin k) (b : Fin q) := σ (finProdFinEquiv (a, b))
  refine ⟨fun a x y => ∑ b, if τ a b x = y then 1 else 0, ?_, ?_, ?_⟩
  · intro x y
    calc
      _ = ∑ p : Fin k × Fin q, if τ p.1 p.2 x = y then 1 else 0 :=
        (Fintype.sum_prod_type _).symm
      _ = ∑ c, if σ c x = y then 1 else 0 :=
        finProdFinEquiv.sum_comp (fun c => if σ c x = y then 1 else 0)
      _ = M x y := (hσ x y).symm
  · intro a x
    rw [Finset.sum_comm]
    simp
  · intro a y
    rw [Finset.sum_comm]
    simp only [← Equiv.eq_symm_apply]
    simp

/-- Distinct parallel copies are separate edges. -/
abbrev BipartiteEdges {X Y : Type*} (M : X → Y → ℕ) := Σ x, Σ y, Fin (M x y)

/-- A proper edge colouring of the actual multigraph edge set. Equality of
colours and a common endpoint force equality of the edges, including the
parallel-copy index. -/
theorem bipartiteMultigraph_properEdgeColouring
    {X Y : Type*} [Fintype X] [Fintype Y]
    (d : ℕ) (M : X → Y → ℕ)
    (hrow : ∀ x, ∑ y, M x y ≤ d)
    (hcol : ∀ y, ∑ x, M x y ≤ d) :
    ∃ colour : BipartiteEdges M → Fin d,
      ∀ e f, colour e = colour f →
        (e.1 = f.1 ∨ e.2.1 = f.2.1) → e = f := by
  classical
  obtain ⟨R, hR, hright, hleft⟩ := bipartiteMultigraph_edgeColouring d M hrow hcol
  have hcard (x : X) (y : Y) :
      Fintype.card {c : Fin d // R c x y} = M x y := by
    simpa only [Nat.card_eq_fintype_card] using hR x y
  let E (x : X) (y : Y) : Fin (M x y) ≃ {c : Fin d // R c x y} :=
    (finCongr (hcard x y).symm).trans (Fintype.equivFin _).symm
  let colour : BipartiteEdges M → Fin d :=
    fun e => (E e.1 e.2.1 e.2.2).val
  refine ⟨colour, ?_⟩
  intro e f hc he
  rcases e with ⟨x, y, i⟩
  rcases f with ⟨z, w, j⟩
  change (E x y i).val = (E z w j).val at hc
  have hx : x = z := by
    rcases he with h | h
    · exact h
    · change y = w at h
      subst w
      exact hleft _ x z y (E x y i).property (hc.symm ▸ (E z y j).property)
  subst z
  have hy : y = w :=
    hright _ x y w (E x y i).property (hc.symm ▸ (E x w j).property)
  subst w
  have hij : i = j := (E x y).injective (Subtype.ext hc)
  subst j
  rfl

end Oberwolfach
