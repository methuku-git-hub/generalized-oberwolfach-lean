module

public import Oberwolfach.ExtendingListPathEmbedding

@[expose] public section
/-! A cycle with one prescribed vertex: its two boundary labels coincide,
so first embed one neighbour and then join distinct endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem extending_list_embed_pinned_cycle (D:V→V→Prop) (L:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (M:ℝ) (hM:0≤M)
    (hdeg:∀ v,(F.degree v:ℝ)≤M) (B:Finset V) (x:V) (ℓ:ℕ) (hℓ:3≤ℓ)
    (hbudget:(B.card:ℝ)+ℓ+2+2*M<β*Fintype.card V):
    ∃ xs:List V,xs.length=ℓ-1 ∧ xs.Nodup ∧
      (∀ z∈xs,z∈L ∧ z∉B ∧ z≠x) ∧ DirectedPathThrough D F x x xs := by
  let B₀:=insert x B
  have hB₀:(B₀.card:ℝ)≤B.card+1:=by exact_mod_cast Finset.card_insert_le x B
  have hchoice:(B₀.card:ℝ)+F.degree x<β*Fintype.card V:=by
    have hx:=hdeg x
    nlinarith
  obtain ⟨y,hyL,hyB,hdxy,hFxy⟩:=extending_list_one_arc_choice D L B₀ β hext F x true hchoice
  have hyB':y∉B:=fun h=>hyB (by simp [B₀,h])
  have hyx:y≠x:=by intro h;subst y;apply hyB;simp [B₀]
  have hbudget':(B₀.card:ℝ)+((ℓ-3)+1:ℕ)+2+2*M<β*Fintype.card V:=by
    have hh:((ℓ-3)+1:ℕ)≤ℓ-2:=by omega
    have hhR:(((ℓ-3)+1:ℕ):ℝ)≤((ℓ-2:ℕ):ℝ):=by exact_mod_cast hh
    have hsub:((ℓ-2:ℕ):ℝ)+2=ℓ:=by exact_mod_cast Nat.sub_add_cancel (by omega:2≤ℓ)
    nlinarith
  obtain ⟨zs,hzslen,hzsnodup,hzs,hchain⟩:=extending_list_embed_internal_path D L β hext F M hM hdeg (ℓ-3) B₀ y x hyx hbudget'
  have hzy:y∉zs:=by intro hz;exact (hzs y hz).2.2.1 rfl
  refine ⟨y::zs,?_,List.nodup_cons.mpr ⟨hzy,hzsnodup⟩,?_,?_⟩
  · simp only [List.length_cons,hzslen];omega
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hyL,hyB',hyx⟩
    obtain ⟨hzL,hzB₀,_,hzx⟩:=hzs z hz
    exact ⟨hzL,fun h=>hzB₀ (by simp [B₀,h]),hzx⟩
  · exact ⟨hdxy,hFxy,hchain⟩
end Oberwolfach
