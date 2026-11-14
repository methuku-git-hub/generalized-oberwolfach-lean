module

public import Oberwolfach.ResidualMarkerCount

@[expose] public section
/-! Bound the number of runs by the number of unselected segments. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_run_start_mem (T:Finset ℕ) (j:ℕ):
    j∈selectedRunStarts T ↔ j∈T ∧ (j=0 ∨ j-1∉T) := by
  simp only [selectedRunStarts, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hj,hn⟩
    refine ⟨hj,?_⟩
    by_cases h0:j=0
    · exact Or.inl h0
    · exact Or.inr (fun hp=>hn ⟨hj,by omega,hp⟩)
  · rintro ⟨hj,h⟩
    refine ⟨hj,?_⟩
    rintro ⟨_,hp,hprev⟩
    rcases h with h0|hprev'
    · omega
    · exact hprev' hprev

theorem selected_run_starts_nonempty (T:Finset ℕ) (hT:T.Nonempty):
    (selectedRunStarts T).Nonempty := by
  let j:=T.min' hT
  have hj:j∈T:=Finset.min'_mem T hT
  refine ⟨j,(selected_run_start_mem T j).mpr ⟨hj,?_⟩⟩
  by_cases hj0:j=0
  · exact Or.inl hj0
  · right
    intro hpred
    have hmin:=Finset.min'_le T (j-1) hpred
    omega

theorem selected_run_start_bounds (d:ℕ) (hd:0<d) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (selectedRunStarts T).card ≤ (Finset.range d\T).card+1 ∧
      1 ≤ (selectedRunStarts T).card+(Finset.range d\T).card := by
  let starts:=selectedRunStarts T
  let positive:=starts.erase 0
  let missing:=Finset.range d\T
  have hpositive:∀j∈positive,0<j := by
    intro j hj
    have hh: j≠0 := (Finset.mem_erase.mp hj).1
    omega
  have hinj:Set.InjOn (fun j:ℕ=>j-1) positive := by
    intro a ha b hb h
    have ha':=hpositive a ha
    have hb':=hpositive b hb
    change a-1=b-1 at h
    omega
  have hsub:positive.image (fun j=>j-1)⊆missing := by
    intro x hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    have hjstart:j∈starts := (Finset.mem_erase.mp hj).2
    have hjpos:=hpositive j hj
    have hh: j∈T ∧ (j=0 ∨ j-1∉T) := (selected_run_start_mem T j).mp hjstart
    have hjd:j<d := by have hz:=hT hh.1;simpa using hz
    have hn:j-1∉T := by
      rcases hh.2 with h|h
      · omega
      · exact h
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),hn⟩
  have hle:positive.card≤missing.card := by
    rw [←Finset.card_image_iff.mpr hinj]
    exact Finset.card_le_card hsub
  have herase:starts.card≤positive.card+1 := by
    dsimp [positive]
    have hh:=Finset.pred_card_le_card_erase (s:=starts) (a:=0)
    omega
  change starts.card≤missing.card+1 ∧ 1≤starts.card+missing.card
  constructor
  · omega
  · by_cases hnon:T.Nonempty
    · have hn:=selected_run_starts_nonempty T hnon
      have hc:0<starts.card := Finset.card_pos.mpr hn
      omega
    · have he:T=∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      have hm:missing.card=d := by simp [missing,he]
      omega
end Oberwolfach
