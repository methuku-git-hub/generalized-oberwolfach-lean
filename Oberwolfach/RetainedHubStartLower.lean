module

public import Oberwolfach.RetentionRestrictionCommonEvent
public import Oberwolfach.RetainedIntervalIdentities
public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.RetainedRawIntervalCardinality

@[expose] public section
/-! The full-row retention test controls how many original starts each hub
loses, even though retention is balanced by start rather than by hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_hub_start_count_lower_from_row_test
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U] [DecidableEq Γ]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t) (ζ:ℝ)
    (hgood:RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (w:U):
    rawIntervalHubStartCount π d g σ w-ζ*Fintype.card V≤
      (Fintype.card (retainedMarkedIndex π d σ g t J w):ℝ):=by
  let Raw:=Finset.univ.filter (fun a=>rawIntervalColouredStart π d (fun e=>σ (w,e)) a g)
  let Keep:=Finset.univ.filter (fun a=>retainedRawStart π d σ g t J w a g)
  let Changes:=Finset.univ.filter (fun a=>retainedRawFamilyState π d σ g t J (a,w)≠rawIntervalFamilyState π d σ (a,w))
  have hkeep:Keep⊆Raw:=by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2.1⟩
  have hlost:Raw\Keep⊆Changes:=by
    intro a ha
    have haRaw:rawIntervalColouredStart π d (fun e=>σ (w,e)) a g:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
    have haNot:¬retainedRawStart π d σ g t J w a g:=by
      intro hh;exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro heq
    have hw0:a∈permutationWindow π 0 (d-1) a:=by
      apply (permutationWindow_mem_iff π 0 (d-1) a a).2
      refine ⟨⟨0,by omega⟩,?_⟩
      simp
    have hraw:rawIntervalFamilyState π d σ (a,w)=some (Sum.inl g):=by
      change rawIntervalState π d (fun e=>σ (w,e)) a=some (Sum.inl g)
      exact (rawIntervalState_interval_iff π d (fun e=>σ (w,e)) a g).2 ⟨a,haRaw,hw0⟩
    have hret:retainedRawFamilyState π d σ g t J (a,w)=some (Sum.inl g):=heq.trans hraw
    change retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ g t J w) a=some (Sum.inl g) at hret
    have hR:∀b h,retainedRawStart π d σ g t J w b h → rawIntervalColouredStart π d (fun e=>σ (w,e)) b h:=fun _ _ hh=>hh.1
    obtain ⟨b,hb,hwin⟩:=(retainedIntervalState_interval_iff π d (fun e=>σ (w,e)) _ hR a g).1 hret
    have hwa:a∈permutationWindow π 0 d a:=permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) a hw0
    have hwb:a∈permutationWindow π 0 d b:=permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) b hwin
    have hab:=rawInterval_coloured_start_unique π d (fun e=>σ (w,e)) a a b g g haRaw hb.1 hwa hwb
    rcases hab with ⟨rfl,_⟩
    exact haNot hb
  have hc:=Finset.card_le_card hlost
  have hsplit:Raw.card=(Raw\Keep).card+Keep.card:=by
    exact (Finset.card_sdiff_add_card_eq_card hkeep).symm
  have hrow:((Changes.card):ℝ)≤ζ*Fintype.card V:=by
    simpa [Changes] using (hgood ()).1 w
  have hRaw:(Raw.card:ℝ)=rawIntervalHubStartCount π d g σ w:=by
    rw [raw_interval_hub_count_eq_card]
    simp [Raw,Fintype.card_subtype]
  have hKeep:(Keep.card:ℝ)=(Fintype.card (retainedMarkedIndex π d σ g t J w):ℝ):=by
    simp [Keep,retainedMarkedIndex,Fintype.card_subtype]
  have hcR:((Raw\Keep).card:ℝ)≤Changes.card:=by exact_mod_cast hc
  have hsR:(Raw.card:ℝ)=((Raw\Keep).card:ℝ)+Keep.card:=by exact_mod_cast hsplit
  linarith
end Oberwolfach
