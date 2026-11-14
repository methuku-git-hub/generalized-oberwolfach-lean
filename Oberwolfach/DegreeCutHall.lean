module

public import Oberwolfach.DenseBipartitePerfectMatching

@[expose] public section

/-! Hall's theorem from linear minimum degree and nonempty large cuts.
The cut assumption is used only after both sides of a failed Hall cut
have been shown to exceed the specified threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem degree_cut_perfect_matching {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X→Y→Prop) (hcard : Fintype.card X=Fintype.card Y)
    (a : ℝ) (ha : 0≤a)
    (hrow : ∀ x,a≤((Finset.univ.filter (E x)).card:ℝ))
    (hcol : ∀ y,a≤((Finset.univ.filter (fun x=>E x y)).card:ℝ))
    (hcut : ∀ S : Finset X,∀ T : Finset Y,a≤(S.card:ℝ) → a≤(T.card:ℝ) →
      S.Nonempty → T.Nonempty → ∃ x∈S,∃ y∈T,E x y) :
    ∃ σ : X≃Y,∀ x,E x (σ x) := by
  classical
  have hhall (S : Finset X) : S.card≤(S.biUnion (fun x=>Finset.univ.filter (E x))).card := by
    let N:=S.biUnion (fun x=>Finset.univ.filter (E x))
    by_contra hfail
    have hlt : N.card<S.card:=lt_of_not_ge hfail
    have hS : S.Nonempty:=Finset.card_pos.mp (by omega)
    obtain ⟨x,hx⟩:=hS
    have hsub : Finset.univ.filter (E x)⊆N:=fun y hy=>Finset.mem_biUnion.mpr ⟨x,hx,hy⟩
    have hSlarge : a≤(S.card:ℝ):=(hrow x).trans ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (Nat.cast_le.mpr hlt.le))
    have hNlt : N.card<Fintype.card Y:=hlt.trans_le (by simpa [hcard] using Finset.card_le_univ S)
    have hT : (Finset.univ\N).Nonempty:=by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
      omega
    obtain ⟨y,hy⟩:=hT
    have hnot : y∉N:=(Finset.mem_sdiff.mp hy).2
    have hsub' : Finset.univ.filter (fun x=>E x y)⊆Finset.univ\S:=by
      intro x hx'
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hxS
      exact hnot (Finset.mem_biUnion.mpr ⟨x,hxS,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx').2⟩⟩)
    have hcomp : (Finset.univ\S).card≤(Finset.univ\N).card:=by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Finset.card_univ,hcard]
      omega
    have hTlarge : a≤((Finset.univ\N).card:ℝ):=(hcol y).trans ((Nat.cast_le.mpr (Finset.card_le_card hsub')).trans (Nat.cast_le.mpr hcomp))
    obtain ⟨x',hx',y',hy',he⟩:=hcut S (Finset.univ\N) hSlarge hTlarge ⟨x,hx⟩ ⟨y,hy⟩
    exact (Finset.mem_sdiff.mp hy').2 (Finset.mem_biUnion.mpr ⟨x',hx',Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩)
  obtain ⟨f,hf,hE⟩:=(Finset.all_card_le_biUnion_card_iff_existsInjective' (fun x=>Finset.univ.filter (E x))).mp hhall
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),fun x=>(Finset.mem_filter.mp (hE x)).2⟩

end Oberwolfach
