module

public import Oberwolfach.BipartiteEdgeColouring

@[expose] public section

/-! Hall's theorem for balanced bipartite graphs of minimum degree at least
half the part size, including the empty graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem dense_bipartite_perfect_matching {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X→Y→Prop) (hcard : Fintype.card X=Fintype.card Y)
    (hrow : ∀ x,Fintype.card Y≤2*(Finset.univ.filter (E x)).card)
    (hcol : ∀ y,Fintype.card X≤2*(Finset.univ.filter (fun x=>E x y)).card) :
    ∃ σ : X≃Y,∀ x,E x (σ x) := by
  classical
  have hhall (S : Finset X) : S.card≤(S.biUnion (fun x=>Finset.univ.filter (E x))).card := by
    let N := S.biUnion (fun x=>Finset.univ.filter (E x))
    rcases S.eq_empty_or_nonempty with rfl|hS
    · simp
    by_cases hsmall : 2*S.card≤Fintype.card Y
    · obtain ⟨x,hx⟩ := hS
      have hsub : Finset.univ.filter (E x)⊆N :=
        fun y hy=>Finset.mem_biUnion.mpr ⟨x,hx,hy⟩
      have hn := Finset.card_le_card hsub
      have hd := hrow x
      change S.card≤N.card
      omega
    · have he : N=Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro y
        by_contra hy
        have hsub : Finset.univ.filter (fun x=>E x y)⊆Finset.univ\S := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
          intro hxS
          exact hy (Finset.mem_biUnion.mpr ⟨x,hxS,Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩⟩)
        have hh := Finset.card_le_card hsub
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ] at hh
        have hd := hcol y
        have hSle := Finset.card_le_univ S
        omega
      change S.card≤N.card
      rw [he,Finset.card_univ,← hcard]
      exact Finset.card_le_univ S
  obtain ⟨f,hf,hE⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun x=>Finset.univ.filter (E x))).mp hhall
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),
    fun x=>(Finset.mem_filter.mp (hE x)).2⟩

end Oberwolfach
