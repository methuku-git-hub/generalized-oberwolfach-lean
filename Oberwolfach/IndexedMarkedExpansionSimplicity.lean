module

public import Oberwolfach.IndexedMarkedExpansion

@[expose] public section

/-! The actual expansion removes formal loops and repeated endpoint pairs.
No simplicity assumption on the original indexed graph is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

theorem indexedMarkedExpansion_no_loops (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    ∀ a,(indexedMarkedExpansion G m hm).src a≠(indexedMarkedExpansion G m hm).dst a:=by
  rintro (a|⟨a|s,k⟩)
  · simp
  · simp only [indexedMarkedExpansion_src_private,indexedMarkedExpansion_dst_private_rim]
    split
    · simp
    · intro he
      exact finRotate_ne_self_of_pos (by omega) k (congrArg Prod.snd (Sum.inr.inj he))
  · simp only [indexedMarkedExpansion_src_private,indexedMarkedExpansion_dst_private_spoke]
    intro he
    exact finRotate_ne_self_of_pos (by omega) k (congrArg Prod.snd (Sum.inr.inj he))

theorem indexedMarkedExpansion_rim_injective (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    Function.Injective (fun a=>((indexedMarkedExpansion G m hm).src a,(indexedMarkedExpansion G m hm).dst a)):=by
  rintro (a|⟨i,k⟩) (a'|⟨i',k'⟩) he
  · have hh:=congrArg Prod.snd he
    simp only [indexedMarkedExpansion_dst_old,Sum.inr.injEq,Prod.mk.injEq,Sum.inl.injEq] at hh
    exact congrArg Sum.inl hh.1
  · have hh:=congrArg Prod.fst he
    simp only [indexedMarkedExpansion_src_old,indexedMarkedExpansion_src_private] at hh
    cases hh
  · have hh:=congrArg Prod.fst he
    simp only [indexedMarkedExpansion_src_old,indexedMarkedExpansion_src_private] at hh
    cases hh
  · exact congrArg Sum.inr (Sum.inr.inj (congrArg Prod.fst he))

theorem indexedMarkedExpansion_spoke_injective (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    Function.Injective (fun s=>((indexedMarkedExpansion G m hm).row s,(indexedMarkedExpansion G m hm).hub s)):=by
  rintro (s|⟨i,k⟩) (s'|⟨i',k'⟩) he
  · have hh:=congrArg Prod.snd he
    simp only [indexedMarkedExpansion_hub_old,Sum.inr.injEq] at hh
    exact congrArg Sum.inl hh
  · have hh:=congrArg Prod.fst he
    simp only [indexedMarkedExpansion_row_old,indexedMarkedExpansion_row_private] at hh
    cases hh
  · have hh:=congrArg Prod.fst he
    simp only [indexedMarkedExpansion_row_old,indexedMarkedExpansion_row_private] at hh
    cases hh
  · exact congrArg Sum.inr (Sum.inr.inj (congrArg Prod.fst he))

theorem indexedMarkedExpansion_no_old_rim (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (v w:V) (a:A⊕((A⊕S)×Fin (m+1))):
    ¬((indexedMarkedExpansion G m hm).src a=Sum.inl v∧(indexedMarkedExpansion G m hm).dst a=Sum.inl w):=by
  cases a with
  | inl a=>simp
  | inr p=>rcases p with ⟨i,k⟩;simp

theorem indexedMarkedExpansion_no_old_spoke (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (v:V) (u:U) (s:S⊕((A⊕S)×Fin (m+1))):
    ¬((indexedMarkedExpansion G m hm).row s=Sum.inl v∧(indexedMarkedExpansion G m hm).hub s=Sum.inl u):=by
  cases s with
  | inl s=>simp
  | inr p=>rcases p with ⟨i,k⟩;simp

end Oberwolfach
