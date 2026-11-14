module

public import Oberwolfach.ExtendingListStability
public import Oberwolfach.Definitions

@[expose] public section
/-! The one- and two-arc choices used when embedding a path or cycle,
avoiding both used labels and already used physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem extending_list_two_arc_choice (D:V→V→Prop) (L B:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (x y:V) (hxy:x≠y)
    (hbudget:(B.card:ℝ)+F.degree x+F.degree y<β*Fintype.card V):
    ∃ z∈L,z∉B ∧ D x z ∧ D z y ∧ ¬F.Adj x z ∧ ¬F.Adj y z := by
  let C:=directedOutNeighbours D x∩directedInNeighbours D y∩L
  let T:=B∪F.neighborFinset x∪F.neighborFinset y
  have hcard:(T.card:ℝ)≤(B.card:ℝ)+F.degree x+F.degree y:=by
    have h₁:=Finset.card_union_le (B∪F.neighborFinset x) (F.neighborFinset y)
    have h₂:=Finset.card_union_le B (F.neighborFinset x)
    have hh:T.card≤B.card+F.degree x+F.degree y:=by
      dsimp [T]
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using (by omega :
        ((B∪F.neighborFinset x)∪F.neighborFinset y).card≤
          B.card+(F.neighborFinset x).card+(F.neighborFinset y).card)
    exact_mod_cast hh
  have hnot:¬C⊆T:=by
    intro hsub
    have hh:C.card≤T.card:=Finset.card_le_card hsub
    have hhR:(C.card:ℝ)≤T.card:=by exact_mod_cast hh
    have hlo:β*Fintype.card V≤(C.card:ℝ):=hext.2.2.2 x y hxy
    linarith
  obtain ⟨z,hzC,hzT⟩:=Finset.not_subset.mp hnot
  have hz:=Finset.mem_inter.mp hzC
  have hzpair:=Finset.mem_inter.mp hz.1
  have hzout:D x z:=(Finset.mem_filter.mp hzpair.1).2
  have hzin:D z y:=(Finset.mem_filter.mp hzpair.2).2
  have hzB:z∉B:=fun h=>hzT (by simp [T,h])
  have hzFx:¬F.Adj x z:=fun h=>hzT (by simp [T,h])
  have hzFy:¬F.Adj y z:=fun h=>hzT (by simp [T,h])
  exact ⟨z,hz.2,hzB,hzout,hzin,hzFx,hzFy⟩
end Oberwolfach
