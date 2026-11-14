module

public import Oberwolfach.PrescribedPositionClosedNeighbourhood

@[expose] public section
/-! Greedily choose mutually nonadjacent vertices outside a previously
excluded set in a degree-two graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

def prescribedSinglesApart (Q:SimpleGraph X) (x y:X):Prop:=
  y∉prescribedClosedNeighbourhood Q x

theorem prescribed_position_greedy_singles (Q:SimpleGraph X) (hdeg:∀ x,Q.degree x≤2):
    ∀ z:ℕ,∀ S:Finset X,S.card+3*z≤Fintype.card X→
      ∃ vs:List X,vs.length=z ∧ (∀ v∈vs,v∉S) ∧ vs.Pairwise (prescribedSinglesApart Q) := by
  intro z
  induction z with
  | zero => intro S h;exact ⟨[],rfl,by simp,by simp⟩
  | succ z ih =>
    intro S h
    have hlt:S.card<Fintype.card X:=by omega
    have hnot:¬(Finset.univ:Finset X)⊆S:=by
      intro hs
      have hh:=Finset.card_le_card hs
      simp only [Finset.card_univ] at hh
      omega
    obtain ⟨x,_,hx⟩:=Finset.not_subset.mp hnot
    let T:=S∪prescribedClosedNeighbourhood Q x
    have hT:T.card≤S.card+3:=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (prescribed_closed_neighbourhood_card Q hdeg x) _)
    have hbudget:T.card+3*z≤Fintype.card X:=by omega
    obtain ⟨rest,hlen,hrest,hpair⟩:=ih T hbudget
    refine ⟨x::rest,by simp [hlen],?_,?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with hy|hy
      · subst y;exact hx
      · intro hyS;exact hrest y hy (Finset.mem_union_left _ hyS)
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hpair⟩
      intro y hy hclose
      exact hrest y hy (Finset.mem_union_right _ hclose)
end Oberwolfach
