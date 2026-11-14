module

public import Oberwolfach.DenseBipartitePerfectMatching

@[expose] public section

/-! Hall's theorem when the forbidden pairs form a partial matching.
The rectangular form is needed before assigning the remaining marked
transformer incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem injection_avoiding_partial_matching {X Y:Type*} [Fintype X] [Fintype Y]
    (Bad:X→Y→Prop)
    (hrow:∀ x,(Finset.univ.filter (Bad x)).card≤1)
    (hcol:∀ y,(Finset.univ.filter (fun x=>Bad x y)).card≤1)
    (hsize:Fintype.card X≤Fintype.card Y)
    (hnotone:2≤Fintype.card Y ∨ Fintype.card X=0):
    ∃ f:X↪Y,∀ x,¬Bad x (f x):=by
  classical
  let C:X→Finset Y:=fun x=>Finset.univ.filter (fun y=>¬Bad x y)
  have hhall (S:Finset X):S.card≤(S.biUnion C).card:=by
    rcases S.eq_empty_or_nonempty with rfl|hS
    · simp
    obtain ⟨x,hx⟩:=hS
    have hY:2≤Fintype.card Y:=by
      rcases hnotone with h|h
      · exact h
      · have hp:=Fintype.card_pos_iff.mpr (show Nonempty X from ⟨x⟩)
        omega
    by_cases hSone:S.card=1
    · have hc:1≤(C x).card:=by
        have hh:=Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=Bad x)
        have hr:=hrow x
        simp only [Finset.card_univ] at hh
        dsimp [C]
        omega
      have hs:C x⊆S.biUnion C:=fun y hy=>Finset.mem_biUnion.mpr ⟨x,hx,hy⟩
      rw [hSone]
      exact hc.trans (Finset.card_le_card hs)
    · have htwo:2≤S.card:=by have hp:=Finset.card_pos.mpr ⟨x,hx⟩;omega
      have hfull:S.biUnion C=Finset.univ:=by
        apply Finset.eq_univ_of_forall
        intro y
        by_contra hy
        have hs:S⊆Finset.univ.filter (fun x=>Bad x y):=by
          intro z hz
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          by_contra hbad
          exact hy (Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩⟩)
        have hh:=Finset.card_le_card hs
        have hc:=hcol y
        omega
      rw [hfull,Finset.card_univ]
      exact (Finset.card_le_univ S).trans hsize
  obtain ⟨f,hf,hfC⟩:=(Finset.all_card_le_biUnion_card_iff_existsInjective' C).mp hhall
  exact ⟨⟨f,hf⟩,fun x=>(Finset.mem_filter.mp (hfC x)).2⟩

 theorem bijection_avoiding_partial_matching {X Y:Type*} [Fintype X] [Fintype Y]
    (Bad:X→Y→Prop)
    (hrow:∀ x,(Finset.univ.filter (Bad x)).card≤1)
    (hcol:∀ y,(Finset.univ.filter (fun x=>Bad x y)).card≤1)
    (hsize:Fintype.card X=Fintype.card Y)
    (hnotone:Fintype.card Y≠1):
    ∃ f:X≃Y,∀ x,¬Bad x (f x):=by
  obtain ⟨f,hf⟩:=injection_avoiding_partial_matching Bad hrow hcol (Nat.le_of_eq hsize)
    (by omega)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective,hsize⟩),hf⟩

end Oberwolfach
