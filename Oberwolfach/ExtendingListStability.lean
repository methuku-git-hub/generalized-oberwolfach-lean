module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! The manuscript's extending-list inequalities, and their stability under
realised changes to directed neighbourhoods and the list itself. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def directedOutNeighbours (D:V→V→Prop) (x:V):Finset V:=Finset.univ.filter (D x)
def directedInNeighbours (D:V→V→Prop) (x:V):Finset V:=Finset.univ.filter (fun y=>D y x)

def IsExtendingList (D:V→V→Prop) (L:Finset V) (lam:ℝ):Prop:=
  0≤lam ∧ lam*Fintype.card V≤(L.card:ℝ) ∧
  (∀ x,lam*Fintype.card V≤((directedOutNeighbours D x∩L).card:ℝ) ∧
        lam*Fintype.card V≤((directedInNeighbours D x∩L).card:ℝ)) ∧
  ∀ x y,x≠y→lam*Fintype.card V≤
    ((directedOutNeighbours D x∩directedInNeighbours D y∩L).card:ℝ)

private theorem card_triple_intersection_loss (A B C A' B' C':Finset V):
    (A∩B∩C).card≤(A'∩B'∩C').card+(A\A').card+(B\B').card+(C\C').card := by
  have hsub:A∩B∩C⊆(A'∩B'∩C')∪(A\A')∪(B\B')∪(C\C'):=by
    intro x hx
    simp only [Finset.mem_inter] at hx
    by_cases ha:x∈A' <;> by_cases hb:x∈B' <;> by_cases hc:x∈C' <;>
      simp [ha,hb,hc,hx.1.1,hx.1.2,hx.2]
  have hh:=Finset.card_le_card hsub
  have h₁:=Finset.card_union_le ((A'∩B'∩C')∪(A\A')∪(B\B')) (C\C')
  have h₂:=Finset.card_union_le ((A'∩B'∩C')∪(A\A')) (B\B')
  have h₃:=Finset.card_union_le (A'∩B'∩C') (A\A')
  omega

theorem extending_list_after_neighbourhood_changes
    (D D':V→V→Prop) (L L':Finset V) (β lam r s:ℝ)
    (hlam:0≤lam) (hr:0≤r) (hs:0≤s)
    (hL:((L\L').card:ℝ)≤s)
    (hout:∀ x,((directedOutNeighbours D x\directedOutNeighbours D' x).card:ℝ)≤r)
    (hin:∀ x,((directedInNeighbours D x\directedInNeighbours D' x).card:ℝ)≤r)
    (hbudget:lam*Fintype.card V+2*r+s≤β*Fintype.card V)
    (hext:IsExtendingList D L β):IsExtendingList D' L' lam := by
  refine ⟨hlam,?_,?_,?_⟩
  · have hh:=card_triple_intersection_loss (Finset.univ:Finset V) Finset.univ L Finset.univ Finset.univ L'
    simp only [Finset.univ_inter,Finset.sdiff_self,Finset.card_empty,zero_add] at hh
    have hh':(L.card:ℝ)≤L'.card+(L\L').card:=by exact_mod_cast hh
    nlinarith [hext.2.1]
  · intro x
    have ho:=card_triple_intersection_loss (directedOutNeighbours D x) Finset.univ L
      (directedOutNeighbours D' x) Finset.univ L'
    have hi:=card_triple_intersection_loss (directedInNeighbours D x) Finset.univ L
      (directedInNeighbours D' x) Finset.univ L'
    simp only [Finset.inter_univ,Finset.sdiff_self,Finset.card_empty,add_zero] at ho hi
    have ho':((directedOutNeighbours D x∩L).card:ℝ)≤
      (directedOutNeighbours D' x∩L').card+(directedOutNeighbours D x\directedOutNeighbours D' x).card+(L\L').card:=by exact_mod_cast ho
    have hi':((directedInNeighbours D x∩L).card:ℝ)≤
      (directedInNeighbours D' x∩L').card+(directedInNeighbours D x\directedInNeighbours D' x).card+(L\L').card:=by exact_mod_cast hi
    exact ⟨by nlinarith [(hext.2.2.1 x).1,hout x],by nlinarith [(hext.2.2.1 x).2,hin x]⟩
  · intro x y hxy
    have hh:=card_triple_intersection_loss (directedOutNeighbours D x) (directedInNeighbours D y) L
      (directedOutNeighbours D' x) (directedInNeighbours D' y) L'
    have hh':((directedOutNeighbours D x∩directedInNeighbours D y∩L).card:ℝ)≤
      (directedOutNeighbours D' x∩directedInNeighbours D' y∩L').card+
      (directedOutNeighbours D x\directedOutNeighbours D' x).card+
      (directedInNeighbours D y\directedInNeighbours D' y).card+(L\L').card:=by exact_mod_cast hh
    nlinarith [hext.2.2.2 x y hxy,hout x,hin y]
end Oberwolfach
