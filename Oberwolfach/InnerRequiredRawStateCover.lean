module

public import Oberwolfach.InnerRequiredTargets
public import Oberwolfach.RetainedIntervalFamily

@[expose] public section
/-! Classify every still-required inner target by the original raw state:
it is unassigned, lost through retention, or an unused ordinary label. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def rawUnassignedAt (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (w:U):Finset V:=
  Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)

def retainedFinalMarkedAt (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U):Finset V:=
  Finset.univ.filter (fun x=>retainedRawFamilyState π d σ false t J (x,w)=some (Sum.inl false))

def rawRetentionChangedAt (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U):Finset V:=
  Finset.univ.filter (fun x=>retainedRawFamilyState π d σ false t J (x,w)≠rawIntervalFamilyState π d σ (x,w))

theorem inner_required_targets_raw_cover
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset V) (absorber occupied unused:U→Finset V)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w):
    ∀w,innerRequiredTargets inner vertices (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t J) absorber occupied w ⊆
      (rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices)∪(unused w∩vertices):=by
  intro w x hx
  by_cases hw:w∈inner
  · simp only [innerRequiredTargets,hw,if_true,Finset.mem_sdiff,Finset.mem_union] at hx
    have hv:=hx.1
    have hR:x∉rawReservedSpokeList π d σ w:=by intro h;exact hx.2 (Or.inl (Or.inl (Or.inl h)))
    have hS:x∉retainedFinalMarkedAt π d σ t J w:=by intro h;exact hx.2 (Or.inl (Or.inl (Or.inr h)))
    have hO:x∉occupied w:=by intro h;exact hx.2 (Or.inr h)
    cases hs:rawIntervalFamilyState π d σ (x,w) with
    | none =>
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨by simp [rawUnassignedAt,hs],hv⟩))
    | some y =>
      cases y with
      | inl g =>
        cases g with
        | false =>
          by_cases hchange:retainedRawFamilyState π d σ false t J (x,w)=rawIntervalFamilyState π d σ (x,w)
          · have hm:x∈retainedFinalMarkedAt π d σ t J w:=by simp [retainedFinalMarkedAt,hchange,hs]
            exact (hS hm).elim
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨by simp [rawRetentionChangedAt,hchange],hv⟩))
        | true => exact (hO (happrox w x hs)).elim
      | inr color =>
        cases color with
        | false =>
          have hm:x∈rawReservedSpokeList π d σ w:=by simp [rawReservedSpokeList,rawIntervalOrdinaryOuter,hs]
          exact (hR hm).elim
        | true =>
          rcases hordinary w x hs with ho|hu
          · exact (hO ho).elim
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu,hv⟩)
  · simp [innerRequiredTargets,hw] at hx
end Oberwolfach
