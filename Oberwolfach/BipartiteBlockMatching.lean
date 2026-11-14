module

public import Oberwolfach.LargeCutDeletion
public import Oberwolfach.BipartiteRelationEmbedding

@[expose] public section

/-! Explicit degree and cut hypotheses on specified parts of an ambient
bipartite relation, and the resulting matching on equal-sized parts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure BipartiteBlockBounds {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X → Y → Prop) (P : X → Prop) (Q : Y → Prop) (d a lam : ℝ) : Prop where
  row : ∀ x, P x → d ≤ ((Finset.univ.filter (fun y => Q y ∧ E x y)).card:ℝ)
  col : ∀ y, Q y → d ≤ ((Finset.univ.filter (fun x => P x ∧ E x y)).card:ℝ)
  cut : ∀ S : Finset X, ∀ T : Finset Y,
    (∀ x∈S, P x) → (∀ y∈T, Q y) → a≤(S.card:ℝ) → a≤(T.card:ℝ) →
    lam*S.card*T.card ≤ (bipartiteMatrixCut (fun x y => if E x y then 1 else 0) S T:ℝ)

theorem subtype_filter_predicate_card {X : Type*} [Fintype X]
    (P R : X → Prop) :
    (Finset.univ.filter (fun x : {x // P x} => R x.val)).card =
      (Finset.univ.filter (fun x => P x ∧ R x)).card := by
  classical
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.property,(Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy h; exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x,(Finset.mem_filter.mp hx).2.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2.2⟩,rfl⟩

theorem bipartite_block_perfect_matching {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X → Y → Prop) (P : X → Prop) (Q : Y → Prop)
    (d a lam : ℝ) (ha : 0<a) (hd : a≤d) (hlam : 0<lam)
    (B : BipartiteBlockBounds E P Q d a lam)
    (hcard : Fintype.card {x // P x}=Fintype.card {y // Q y}) :
    ∃ f : {x // P x} ≃ {y // Q y}, ∀ x, E x.val (f x).val := by
  classical
  apply degree_cut_perfect_matching (fun x : {x // P x} => fun y : {y // Q y} => E x.val y.val)
    hcard a ha.le
  · intro x
    rw [subtype_filter_predicate_card]
    exact hd.trans (B.row x.val x.property)
  · intro y
    have hc := subtype_filter_predicate_card P (fun x => E x y.val)
    have hh := hd.trans (B.col y.val y.property)
    rw [←hc] at hh
    convert hh using 1 <;> congr!
  · intro S T hS hT hSn hTn
    let ex : {x // P x} ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
    let ey : {y // Q y} ↪ Y := ⟨Subtype.val,Subtype.val_injective⟩
    have hP : ∀ x∈S.map ex, P x := by
      intro x hx; obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hx; exact z.property
    have hQ : ∀ y∈T.map ey, Q y := by
      intro y hy; obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hy; exact z.property
    have hc := B.cut (S.map ex) (T.map ey) hP hQ
      (by simpa using hS) (by simpa using hT)
    obtain ⟨x,hx,y,hy,he,hf⟩ := large_cut_after_bounded_deletion E (fun _ _ => False)
      (S.map ex) (T.map ey) a 0 lam ha hlam (by positivity)
      (by simpa using hS) (by simpa using hT) (by intro x; simp) hc
    obtain ⟨x',hx',rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_map.mp hy
    exact ⟨x',hx',y',hy',he⟩

theorem block_row_le_full {X Y : Type*} [Fintype Y]
    (E : X → Y → Prop) (Q : Y → Prop) (x : X) :
    (Finset.univ.filter (fun y => Q y ∧ E x y)).card ≤ (Finset.univ.filter (E x)).card := by
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2.2⟩

end Oberwolfach
