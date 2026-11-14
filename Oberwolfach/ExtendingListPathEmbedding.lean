module

public import Oberwolfach.ExtendingListGreedyOneChoice

@[expose] public section
/-! Embed a whole path between two prescribed distinct endpoints, avoiding
used labels and forbidden physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def DirectedPathThrough (D:V→V→Prop) (F:SimpleGraph V) (x y:V):List V→Prop
  | []=>D x y ∧ ¬F.Adj x y
  | z::zs=>D x z ∧ ¬F.Adj x z ∧ DirectedPathThrough D F z y zs

theorem extending_list_embed_internal_path (D:V→V→Prop) (L:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (M:ℝ) (hM:0≤M)
    (hdeg:∀ v,(F.degree v:ℝ)≤M) :
    ∀ k:ℕ,∀ (B:Finset V) (x y:V),x≠y→
      (B.card:ℝ)+(k+1:ℕ)+2+2*M<β*Fintype.card V→
      ∃ xs:List V,xs.length=k+1 ∧ xs.Nodup ∧
        (∀ z∈xs,z∈L ∧ z∉B ∧ z≠x ∧ z≠y) ∧ DirectedPathThrough D F x y xs := by
  intro k
  induction k with
  | zero =>
    intro B x y hxy hbudget
    let B₀:=insert x (insert y B)
    have hB₀:(B₀.card:ℝ)≤B.card+2:=by
      have h₁:=Finset.card_insert_le x (insert y B)
      have h₂:=Finset.card_insert_le y B
      have hh:B₀.card≤B.card+2:=by dsimp [B₀];omega
      exact_mod_cast hh
    have hchoice:(B₀.card:ℝ)+F.degree x+F.degree y<β*Fintype.card V:=by
      have hx:=hdeg x;have hy:=hdeg y
      norm_num at hbudget ⊢
      linarith
    obtain ⟨z,hzL,hzB,hxz,hzy,hFx,hFy⟩:=extending_list_two_arc_choice D L B₀ β hext F x y hxy hchoice
    have hzB':z∉B:=fun h=>hzB (by simp [B₀,h])
    have hzx:z≠x:=by intro h;subst z;apply hzB;simp [B₀]
    have hzy':z≠y:=by intro h;subst z;apply hzB;simp [B₀]
    refine ⟨[z],by simp,by simp,?_,?_⟩
    · intro z' hz'
      simp only [List.mem_singleton] at hz'
      subst z'
      exact ⟨hzL,hzB',hzx,hzy'⟩
    · exact ⟨hxz,hFx,hzy,fun h=>hFy h.symm⟩
  | succ k ih =>
    intro B x y hxy hbudget
    let B₀:=insert x (insert y B)
    have hB₀:(B₀.card:ℝ)≤B.card+2:=by
      have h₁:=Finset.card_insert_le x (insert y B)
      have h₂:=Finset.card_insert_le y B
      have hh:B₀.card≤B.card+2:=by dsimp [B₀];omega
      exact_mod_cast hh
    have hchoice:(B₀.card:ℝ)+F.degree x<β*Fintype.card V:=by
      have hx:=hdeg x
      push_cast at hbudget
      nlinarith
    obtain ⟨z,hzL,hzB,hxz,hFx⟩:=extending_list_one_arc_choice D L B₀ β hext F x true hchoice
    have hzB':z∉B:=fun h=>hzB (by simp [B₀,h])
    have hzx:z≠x:=by intro h;subst z;apply hzB;simp [B₀]
    have hzy:z≠y:=by intro h;subst z;apply hzB;simp [B₀]
    let B':=insert x B
    have hB':(B'.card:ℝ)≤B.card+1:=by exact_mod_cast Finset.card_insert_le x B
    have hbudget':(B'.card:ℝ)+(k+1:ℕ)+2+2*M<β*Fintype.card V:=by
      push_cast at hbudget ⊢
      nlinarith
    obtain ⟨xs,hxslen,hxsnodup,hxs,hchain⟩:=ih B' z y hzy hbudget'
    have hzn:z∉xs:=by
      intro hz
      exact (hxs z hz).2.2.1 rfl
    refine ⟨z::xs,?_,List.nodup_cons.mpr ⟨hzn,hxsnodup⟩,?_,?_⟩
    · simp only [List.length_cons,hxslen]
    · intro w hw
      rcases List.mem_cons.mp hw with hw | hw
      · subst w;exact ⟨hzL,hzB',hzx,hzy⟩
      · obtain ⟨hwL,hwB',hwz,hwy⟩:=hxs w hw
        have hwx:w≠x:=by intro he;subst w;apply hwB';simp [B']
        have hwB:w∉B:=fun he=>hwB' (by simp [B',he])
        exact ⟨hwL,hwB,hwx,hwy⟩
    · exact ⟨hxz,hFx,hchain⟩
end Oberwolfach
