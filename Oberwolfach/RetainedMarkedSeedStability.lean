module

public import Oberwolfach.TypedMarkedPotentialDeletion
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! An all-root seed load survives start retention with the realised
row and column loss, without changing its original target or weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}
  {H₀ Hₖ:V→U→Prop}

theorem retained_marked_seed_load_stability
    (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ Hₖ→ℝ) (B ζ:ℝ) (hB:0≤B) (hζ:0≤ζ)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R:E⊕K→Prop) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (good:RetainedRestrictionGood π d σ g₀ t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (g:Γ) (j:Color) (root:(E⊕K)⊕(Bool×V×U)):
    |typedMarkedPotentialLoad w R (retainedRawMarkedSpokes π d σ g₀ t J g j) root-
      typedMarkedPotentialLoad w R (rawMarkedSpokes π d σ g j) root|≤
      11*((m:ℝ)+1)^4*B*ζ := by
  have hc:=retainedMarkedSpokes_restriction_changes π d σ g₀ t J
    (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ good g j ()
  have hcol : ∀ a u,(∑ v,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤ζ*(Fintype.card V:ℝ) := by
    intro a u
    simpa using hc.1 a u
  have hrow : ∀ a v,(∑ u,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤ζ*(Fintype.card V:ℝ) := by
    intro a v
    have hh : (∑ u,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
        retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤ζ*(Fintype.card U:ℝ) := by
      simpa using hc.2 a v
    have hcard:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
    exact hh.trans (mul_le_mul_of_nonneg_left hcard hζ)
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hh:=typedMarkedPotentialLoad_degree_stability hm hn hu w B hB hw R R
    (rawMarkedSpokes π d σ g j) (retainedRawMarkedSpokes π d σ g₀ t J g j)
    (ζ*(Fintype.card V:ℝ)) (mul_nonneg hζ hnpos.le)
    (by intro x;simp;positivity) (by intro x;simp;positivity) hrow hcol root
  have heq:11*((m:ℝ)+1)^4*B*(ζ*(Fintype.card V:ℝ))/Fintype.card V=
      11*((m:ℝ)+1)^4*B*ζ := by field_simp
  simpa only [heq] using hh
end Oberwolfach
