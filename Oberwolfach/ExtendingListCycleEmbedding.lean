module

public import Oberwolfach.ExtendingListPathEmbedding

@[expose] public section
/-! Embed one directed cycle using an extending list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def DirectedCycleThrough (D:V→V→Prop) (F:SimpleGraph V):List V→Prop
  | []=>False
  | x::xs=>DirectedPathThrough D F x x xs

theorem extending_list_embed_cycle (D:V→V→Prop) (L:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (M:ℝ) (hM:0≤M)
    (hdeg:∀ v,(F.degree v:ℝ)≤M) (B:Finset V) (ℓ:ℕ) (hℓ:3≤ℓ)
    (hbudget:(B.card:ℝ)+ℓ+2+2*M<β*Fintype.card V):
    ∃ xs:List V,xs.length=ℓ ∧ xs.Nodup ∧
      (∀ z∈xs,z∈L ∧ z∉B) ∧ DirectedCycleThrough D F xs := by
  have hfree:(B.card:ℝ)<β*Fintype.card V:=by nlinarith
  obtain ⟨x,hxL,hxB⟩:=extending_list_free_choice D L B β hext hfree
  let B₀:=insert x B
  have hB₀:(B₀.card:ℝ)≤B.card+1:=by exact_mod_cast Finset.card_insert_le x B
  have hchoice:(B₀.card:ℝ)+F.degree x<β*Fintype.card V:=by
    have hx:=hdeg x
    nlinarith
  obtain ⟨y,hyL,hyB,hdxy,hFxy⟩:=extending_list_one_arc_choice D L B₀ β hext F x true hchoice
  have hyB':y∉B:=fun h=>hyB (by simp [B₀,h])
  have hyx:y≠x:=by intro h;subst y;apply hyB;simp [B₀]
  let B':=insert x (insert y B)
  have hB':(B'.card:ℝ)≤B.card+2:=by
    have h₁:=Finset.card_insert_le x (insert y B)
    have h₂:=Finset.card_insert_le y B
    have hh:B'.card≤B.card+2:=by dsimp [B'];omega
    exact_mod_cast hh
  have hlen:ℓ-3+1=ℓ-2:=by omega
  have hbudget':(B'.card:ℝ)+((ℓ-3)+1:ℕ)+2+2*M<β*Fintype.card V:=by
    have hh:((ℓ-3)+1:ℕ)≤ℓ-2:=by omega
    have hhR:(((ℓ-3)+1:ℕ):ℝ)≤((ℓ-2:ℕ):ℝ):=by exact_mod_cast hh
    have hsub:((ℓ-2:ℕ):ℝ)+2=ℓ:=by exact_mod_cast Nat.sub_add_cancel (by omega:2≤ℓ)
    nlinarith
  obtain ⟨zs,hzslen,hzsnodup,hzs,hchain⟩:=extending_list_embed_internal_path D L β hext F M hM hdeg (ℓ-3) B' y x hyx hbudget'
  have hzx:x∉zs:=by intro hz;exact (hzs x hz).2.2.2 rfl
  have hzy:y∉zs:=by intro hz;exact (hzs y hz).2.2.1 rfl
  refine ⟨x::y::zs,?_,?_,?_,?_⟩
  · simp only [List.length_cons,hzslen];omega
  · exact List.nodup_cons.mpr ⟨by simp [hyx.symm,hzx],List.nodup_cons.mpr ⟨hzy,hzsnodup⟩⟩
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hxL,hxB⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hyL,hyB'⟩
    obtain ⟨hzL,hzB',_,_⟩:=hzs z hz
    exact ⟨hzL,fun h=>hzB' (by simp [B',h])⟩
  · exact ⟨hdxy,hFxy,hchain⟩
end Oberwolfach
