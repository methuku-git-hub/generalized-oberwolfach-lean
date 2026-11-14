module

public import Oberwolfach.ExtendingListOneSidedPath

@[expose] public section
/-! Embed a path with no prescribed endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def DirectedNonemptyPath (D:V→V→Prop) (F:SimpleGraph V) (forward:Bool):List V→Prop
  | []=>False
  | x::xs=>DirectedPathFrom D F forward x xs

theorem extending_list_embed_free_path (D:V→V→Prop) (L:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (M:ℝ) (hM:0≤M)
    (hdeg:∀ v,(F.degree v:ℝ)≤M) (forward:Bool) (k:ℕ) (hk:1≤k)
    (B:Finset V) (hbudget:(B.card:ℝ)+k+2+M<β*Fintype.card V):
    ∃ xs:List V,xs.length=k ∧ xs.Nodup ∧
      (∀ z∈xs,z∈L ∧ z∉B) ∧ DirectedNonemptyPath D F forward xs := by
  have hfree:(B.card:ℝ)<β*Fintype.card V:=by nlinarith
  obtain ⟨x,hxL,hxB⟩:=extending_list_free_choice D L B β hext hfree
  let B':=insert x B
  have hB':(B'.card:ℝ)≤B.card+1:=by exact_mod_cast Finset.card_insert_le x B
  have hbudget':(B'.card:ℝ)+(k-1:ℕ)+1+M<β*Fintype.card V:=by
    have hkR:((k-1:ℕ):ℝ)+1=k:=by exact_mod_cast Nat.sub_add_cancel hk
    nlinarith
  obtain ⟨zs,hzslen,hzsnodup,hzs,hchain⟩:=extending_list_embed_one_sided_path D L β hext F M hM hdeg forward (k-1) B' x hbudget'
  have hzx:x∉zs:=by intro hz;exact (hzs x hz).2.2 rfl
  refine ⟨x::zs,?_,List.nodup_cons.mpr ⟨hzx,hzsnodup⟩,?_,?_⟩
  · simp only [List.length_cons,hzslen];omega
  · intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact ⟨hxL,hxB⟩
    obtain ⟨hzL,hzB',_⟩:=hzs z hz
    exact ⟨hzL,fun h=>hzB' (by simp [B',h])⟩
  · exact hchain
end Oberwolfach
