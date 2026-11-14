module

public import Oberwolfach.OrdinaryRawGlobalDegreeFromProfiles
public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! The actual cleanup profile already contains all three typed edit bounds.
Together with full-domain raw tests, they yield the physical degree cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_physical_degree_cap_from_global_profiles
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH L βe βh Trow Tidx:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw)
    (hTrow:0≤Trow) (hTidx:0≤Tidx) (hL:0≤L)
    (hrows:RawOrdinaryRows P π d 3 Finset.univ pR s j Trow raw)
    (hindices:RawOrdinaryDomainIndices F π d 3 Finset.univ pH j Tidx raw):
    ∃D:ℕ,(∀w:V⊕U,(ordinaryPhysicalGraph Q H).degree w≤D) ∧
      (D:ℝ)≤max ((pR*Fintype.card V+Trow+L)+(pH*Fintype.card U+Tidx+L))
        (pH*Fintype.card V+Trow+L)+1:=by
  have hraw:=ordinary_raw_global_degree_from_profiles P F π d pR pH Trow Tidx s j raw profile.spoke_probability hrows hindices
  have hr:∀v,(Q.degree v:ℝ)≤pR*Fintype.card V+Trow+L:=by
    intro v
    have hv:(P.degree v:ℝ)≤Fintype.card V:=by exact_mod_cast (P.degree_lt_card_verts v).le
    have hm:=mul_le_mul_of_nonneg_left hv profile.rim_nonneg
    have hh:=card_difference_le_changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)
    rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hh
    linarith only [hraw.1 v,hm,(abs_le.mp hh).1,profile.rim_edit v]
  have hs:∀v,((Finset.univ.filter (H v)).card:ℝ)≤pH*Fintype.card U+Tidx+L:=by
    intro v
    have hh:=card_difference_le_changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))
    linarith only [hraw.2.1 v,(abs_le.mp hh).1,profile.spoke_row_edit v]
  have hc:∀u,((Finset.univ.filter (fun v=>H v u)).card:ℝ)≤pH*Fintype.card V+Trow+L:=by
    intro u
    have hh:=card_difference_le_changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>H v u))
    linarith only [hraw.2.2 u,(abs_le.mp hh).1,profile.spoke_column_edit u]
  let b:=max ((pR*Fintype.card V+Trow+L)+(pH*Fintype.card U+Tidx+L)) (pH*Fintype.card V+Trow+L)
  have hpR:=profile.rim_nonneg
  have hpH:=profile.spoke_nonneg
  have hb:0≤b:=by dsimp [b];positivity
  have hdeg:=ordinary_physical_degree_bound Q H
    (pR*Fintype.card V+Trow+L) (pH*Fintype.card U+Tidx+L) (pH*Fintype.card V+Trow+L) b
    hr hs hc (le_max_left _ _) (le_max_right _ _)
  refine ⟨⌈b⌉₊,?_,(Nat.ceil_lt_add_one hb).le⟩
  intro w
  exact_mod_cast (hdeg w).trans (Nat.le_ceil b)
end Oberwolfach
