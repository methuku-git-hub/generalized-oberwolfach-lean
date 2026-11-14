module

public import Oberwolfach.RawIntervalProtectedUnassignedList
public import Oberwolfach.RawIntervalStartColumnCount

@[expose] public section
/-! A protected-list failure at an otherwise unassigned vertex is charged to
an actual interval start at its unique predecessor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_unassigned_not_protected_has_start
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (w:U) (x:V) (hx:rawIntervalFamilyState π d σ (x,w)=none)
    (hnot:x∉rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w):
    rawIntervalColouredStart π d (fun e=>σ (w,e)) ((π^d).symm x) g₀ ∨
      rawIntervalColouredStart π d (fun e=>σ (w,e)) ((π^d).symm x) g₁:=by
  have hend:x∈Finset.univ.image (fun i:retainedAndRawIntervalIndex π d σ g₀ g₁ t J w=>
      (π^d) (retainedAndRawIntervalRoot π d σ g₀ g₁ t J w i)):=by
    have hh:=hnot
    simp only [rawIntervalProtectedUnassignedList,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,not_and] at hh
    exact Classical.byContradiction (hh hx)
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hend
  have hroot:retainedAndRawIntervalRoot π d σ g₀ g₁ t J w i=(π^d).symm x:=by
    apply (π^d).injective
    simpa using hi
  cases i with
  | inl a=>
    left
    rw [←hroot]
    exact a.property.1
  | inr a=>
    right
    rw [←hroot]
    exact a.property
def rawProtectedPairHubs
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (x y:V):Finset U:=
  Finset.univ.filter (fun w=>x∈rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w ∧
    y∈rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w)

theorem raw_protected_pair_hubs_loss_bound
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (x y:V):
    rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ≤
      (rawProtectedPairHubs π d σ g₀ g₁ t J x y).card+
      rawIntervalStartColumnCount π d σ ((π^d).symm x) g₀ Finset.univ+
      rawIntervalStartColumnCount π d σ ((π^d).symm x) g₁ Finset.univ+
      rawIntervalStartColumnCount π d σ ((π^d).symm y) g₀ Finset.univ+
      rawIntervalStartColumnCount π d σ ((π^d).symm y) g₁ Finset.univ:=by
  let A:=Finset.univ.filter (fun w=>rawIntervalFamilyState π d σ (x,w)=none ∧ rawIntervalFamilyState π d σ (y,w)=none)
  let B:=rawProtectedPairHubs π d σ g₀ g₁ t J x y
  let C:=fun v:V=>fun g:Γ=>Finset.univ.filter (fun w=>rawIntervalColouredStart π d (fun e=>σ (w,e)) ((π^d).symm v) g)
  have hsub:A⊆B∪C x g₀∪C x g₁∪C y g₀∪C y g₁:=by
    intro w hw
    have hw':=Finset.mem_filter.mp hw |>.2
    by_cases hx:x∈rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w
    · by_cases hy:y∈rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w
      · simp [B,rawProtectedPairHubs,hx,hy]
      · have h:=raw_unassigned_not_protected_has_start π d σ g₀ g₁ t J w y hw'.2 hy
        rcases h with h|h <;> simp [C,h]
    · have h:=raw_unassigned_not_protected_has_start π d σ g₀ g₁ t J w x hw'.1 hx
      rcases h with h|h <;> simp [C,h]
  have hc:=Finset.card_le_card hsub
  have h1:=Finset.card_union_le B (C x g₀)
  have h2:=Finset.card_union_le (B∪C x g₀) (C x g₁)
  have h3:=Finset.card_union_le (B∪C x g₀∪C x g₁) (C y g₀)
  have h4:=Finset.card_union_le (B∪C x g₀∪C x g₁∪C y g₀) (C y g₁)
  have hcard:A.card≤B.card+(C x g₀).card+(C x g₁).card+(C y g₀).card+(C y g₁).card:=by omega
  have hcardR:(A.card:ℝ)≤B.card+(C x g₀).card+(C x g₁).card+(C y g₀).card+(C y g₁).card:=by exact_mod_cast hcard
  simpa [A,B,C,rawIntervalUnassignedPairColumnCount,rawIntervalStartColumnCount,←Finset.sum_filter] using hcardR
end Oberwolfach
