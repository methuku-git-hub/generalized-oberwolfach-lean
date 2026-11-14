module

public import Oberwolfach.ExtendingListGreedyOneChoice

@[expose] public section
/-! Embed a path forwards or backwards from one prescribed endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def DirectedPathFrom (D:V→V→Prop) (F:SimpleGraph V) (forward:Bool) (x:V):List V→Prop
  | []=>True
  | z::zs=>(if forward then D x z else D z x) ∧ ¬F.Adj x z ∧ DirectedPathFrom D F forward z zs

theorem extending_list_embed_one_sided_path (D:V→V→Prop) (L:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (M:ℝ) (hM:0≤M)
    (hdeg:∀ v,(F.degree v:ℝ)≤M) (forward:Bool):
    ∀ k:ℕ,∀ (B:Finset V) (x:V),
      (B.card:ℝ)+(k:ℝ)+1+M<β*Fintype.card V→
      ∃ xs:List V,xs.length=k ∧ xs.Nodup ∧
        (∀ z∈xs,z∈L ∧ z∉B ∧ z≠x) ∧ DirectedPathFrom D F forward x xs := by
  intro k
  induction k with
  | zero =>
    intro B x hbudget
    exact ⟨[],rfl,by simp,by simp,by trivial⟩
  | succ k ih =>
    intro B x hbudget
    let B₀:=insert x B
    have hB₀:(B₀.card:ℝ)≤B.card+1:=by exact_mod_cast Finset.card_insert_le x B
    have hchoice:(B₀.card:ℝ)+F.degree x<β*Fintype.card V:=by
      have hx:=hdeg x
      push_cast at hbudget
      nlinarith
    obtain ⟨z,hzL,hzB,hDxz,hFx⟩:=extending_list_one_arc_choice D L B₀ β hext F x forward hchoice
    have hzB':z∉B:=fun h=>hzB (by simp [B₀,h])
    have hzx:z≠x:=by intro h;subst z;apply hzB;simp [B₀]
    have hbudget':(B₀.card:ℝ)+(k:ℝ)+1+M<β*Fintype.card V:=by
      push_cast at hbudget
      nlinarith
    obtain ⟨xs,hxslen,hxsnodup,hxs,hchain⟩:=ih B₀ z hbudget'
    have hzn:z∉xs:=by intro hz;exact (hxs z hz).2.2 rfl
    refine ⟨z::xs,?_,List.nodup_cons.mpr ⟨hzn,hxsnodup⟩,?_,?_⟩
    · simp only [List.length_cons,hxslen]
    · intro w hw
      rcases List.mem_cons.mp hw with hw | hw
      · subst w;exact ⟨hzL,hzB',hzx⟩
      · obtain ⟨hwL,hwB₀,hwz⟩:=hxs w hw
        have hwx:w≠x:=by intro he;subst w;apply hwB₀;simp [B₀]
        have hwB:w∉B:=fun he=>hwB₀ (by simp [B₀,he])
        exact ⟨hwL,hwB,hwx⟩
    · exact ⟨hDxz,hFx,hchain⟩
end Oberwolfach
