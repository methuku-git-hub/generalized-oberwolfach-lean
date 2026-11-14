module

public import Oberwolfach.MarkedFiniteBalanceValues

@[expose] public section

/-! Explicit losses for the four balance differences from actual finite
incidence bounds. The hub coefficient m is retained; no sampling density
multiplies a deletion that has already been realised. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteBalance_bound
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (δ:ℝ) (hδ:0≤δ)
    (hA:∀ v,((A.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ)
    (hR:∀ v,((S.filter (fun s=>s.1=v)).card:ℝ)≤δ)
    (hC:∀ u,((S.filter (fun s=>s.2=u)).card:ℝ)≤δ)
    (z:V⊕U) (i:Fin 4):
    |markedFiniteBalance tail head ktail khead HK A S m z i|≤(m+2)*δ:=by
  have hmono {T:Type} (F:Finset T) (p q:T→Prop) [DecidablePred p] [DecidablePred q] (h:∀ a,p a→q a):
      ((F.filter p).card:ℝ)≤(F.filter q).card:=by
    exact_mod_cast Finset.card_le_card (show F.filter p⊆F.filter q from fun a ha=>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,h a (Finset.mem_filter.mp ha).2⟩)
  have hdiff (x y:ℝ) (hx:0≤x) (hxδ:x≤δ) (hy:0≤y) (hyδ:y≤δ):|x-y|≤(m+2)*δ:=by
    have hmδ:0≤(m:ℝ)*δ:=mul_nonneg (Nat.cast_nonneg _) hδ
    exact abs_le.mpr ⟨by nlinarith only [hx,hyδ,hmδ,hδ],by nlinarith only [hy,hxδ,hmδ,hδ]⟩
  cases z with
  | inl v=>
    have ho:= (hmono A (fun a=>Sum.elim tail ktail a=v)
      (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v) (fun _ h=>Or.inl h)).trans (hA v)
    have hi:= (hmono A (fun a=>Sum.elim head khead a=v)
      (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v) (fun _ h=>Or.inr h)).trans (hA v)
    have hk:= (hmono A (fun a=>Sum.elim head khead a=v∧markedArcType a=true)
      (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v) (fun _ h=>Or.inr h.1)).trans (hA v)
    have hs:= (hmono S (fun s=>s.1=v∧HK s.1 s.2) (fun s=>s.1=v) (fun _ h=>h.1)).trans (hR v)
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · exact hdiff _ _ (Nat.cast_nonneg _) ho (Nat.cast_nonneg _) (hR v)
    · exact hdiff _ _ (Nat.cast_nonneg _) hi (Nat.cast_nonneg _) (hR v)
    · exact hdiff _ _ (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) hs
    · simpa only [abs_zero] using (show 0≤(m+2:ℝ)*δ by positivity)
  | inr u=>
    have h0:= (hmono S (fun s=>s.2=u∧¬HK s.1 s.2) (fun s=>s.2=u) (fun _ h=>h.1)).trans (hC u)
    have h1:= (hmono S (fun s=>s.2=u∧HK s.1 s.2) (fun s=>s.2=u) (fun _ h=>h.1)).trans (hC u)
    have hm:(0:ℝ)≤m:=Nat.cast_nonneg _
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ']
    all_goals first | (simpa only [abs_zero] using (show 0≤(m+2:ℝ)*δ by positivity)) | skip
    have hn0:(0:ℝ)≤(S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:=Nat.cast_nonneg _
    have hn1:(0:ℝ)≤(S.filter (fun s=>s.2=u∧HK s.1 s.2)).card:=Nat.cast_nonneg _
    have he:=mul_le_mul_of_nonneg_left h1 hm
    have hp:=mul_nonneg hm hn1
    apply abs_le.mpr
    constructor <;> nlinarith only [h0,h1,hn0,hn1,he,hp,hδ,mul_nonneg hm hδ]

end Oberwolfach
