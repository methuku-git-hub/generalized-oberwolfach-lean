module

public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.RawMarkedResourceCoordinates

@[expose] public section
/-! Global retention tests provide the row and column mismatch bounds for
the identical sample used by the correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_retention_mismatch_from_global_event
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g₀ g:Γ) (j:Color) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀) t)
    (ζ:ℝ) (hζ:0≤ζ) (hU:Fintype.card U≤Fintype.card V)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) g₀ t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) g₀ t J g j;
    (∀b v,((Finset.univ.filter (fun u=>¬(H b v u↔rawMarkedPairSpokes π d raw g j b v u))).card:ℝ)≤ζ*Fintype.card V) ∧
    (∀b u,((Finset.univ.filter (fun v=>¬(H b v u↔rawMarkedPairSpokes π d raw g j b v u))).card:ℝ)≤ζ*Fintype.card V) :=by
  intro H
  have hscale:ζ*(Fintype.card U:ℝ)≤ζ*Fintype.card V:=mul_le_mul_of_nonneg_left (by exact_mod_cast hU) hζ
  constructor
  · intro b v
    have hsub:(Finset.univ.filter (fun u=>¬(H b v u↔rawMarkedPairSpokes π d raw g j b v u)))⊆
        Finset.univ.filter (fun u=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) g₀ t J (v,u)≠rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u)):=by
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
      intro hh
      cases b <;> dsimp [H,retainedRawMarkedSpokes,rawMarkedPairSpokes,rawMarkedSpokes] at hu <;> rw [hh] at hu <;> exact hu ⟨(fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _),(fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)⟩
    have hcard:(((Finset.univ.filter (fun u=>¬(H b v u↔rawMarkedPairSpokes π d raw g j b v u))).card):ℝ)≤
        ((Finset.univ.filter (fun u=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) g₀ t J (v,u)≠rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u))).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    have hh:((Finset.univ.filter (fun u=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) g₀ t J (v,u)≠rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u))).card:ℝ)≤ζ*Fintype.card U:=by simpa only [Finset.card_univ] using (hgood ()).2 v
    exact (hcard.trans hh).trans hscale
  · intro b u
    have hsub:(Finset.univ.filter (fun v=>¬(H b v u↔rawMarkedPairSpokes π d raw g j b v u)))⊆
        Finset.univ.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) g₀ t J (v,u)≠rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u)):=by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      intro hh
      cases b <;> dsimp [H,retainedRawMarkedSpokes,rawMarkedPairSpokes,rawMarkedSpokes] at hv <;> rw [hh] at hv <;> exact hv ⟨(fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _),(fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)⟩
    have hcard:(((Finset.univ.filter (fun v=>¬(H b v u↔rawMarkedPairSpokes π d raw g j b v u))).card):ℝ)≤
        ((Finset.univ.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) g₀ t J (v,u)≠rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u))).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    have hh:((Finset.univ.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) g₀ t J (v,u)≠rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u))).card:ℝ)≤ζ*Fintype.card V:=by simpa only [Finset.card_univ] using (hgood ()).1 u
    exact hcard.trans hh
end Oberwolfach
