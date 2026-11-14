module

public import Oberwolfach.OrdinaryRestrictedChanges

@[expose] public section
/-! Outside the active hub domain, keep the original sampled spokes except
at the finitely many roots. This preserves every root star and charges at
most the number of roots in each outside column. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRootColumnRepair (H J:V→U→Prop) (T:Finset V) (B:Finset U):V→U→Prop:=
  fun v u=>if u∈B ∨ v∈T then J v u else H v u

theorem ordinary_root_column_repair_properties (H J:V→U→Prop) (T:Finset V) (B:Finset U) (L:ℝ)
    (hL:0≤L)
    (hrow:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L)
    (hcol:∀u∈B,((changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    let J':=ordinaryRootColumnRepair H J T B;
    (∀v∈T,∀u,J' v u↔J v u) ∧ (∀u∈B,∀v,J' v u↔J v u) ∧
    (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J' v))).card:ℝ)≤L) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>J' v u))).card:ℝ)≤L+T.card):=by
  intro J'
  have hr:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J' v))).card:ℝ)≤L:=by
    intro v
    have hsub:changed (Finset.univ.filter (H v)) (Finset.univ.filter (J' v))⊆
        changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v)):=by
      intro u hu
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
      by_cases hc:u∈B∨v∈T
      · simpa [J',ordinaryRootColumnRepair,hc] using hu
      · simp [J',ordinaryRootColumnRepair,hc] at hu
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hrow v)
  have hc:∀u,((changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>J' v u))).card:ℝ)≤L+T.card:=by
    intro u
    by_cases hu:u∈B
    · have he:Finset.univ.filter (fun v=>J' v u)=Finset.univ.filter (fun v=>J v u):=by
        ext v;simp [J',ordinaryRootColumnRepair,hu]
      rw [he]
      linarith [hcol u hu]
    · have hsub:changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J' v u))⊆T:=by
        intro v hv
        by_contra hvT
        simp [changed,J',ordinaryRootColumnRepair,hu,hvT] at hv
      have hh:((changed (Finset.univ.filter (fun v=>H v u))
          (Finset.univ.filter (fun v=>J' v u))).card:ℝ)≤T.card:=Nat.cast_le.mpr (Finset.card_le_card hsub)
      linarith
  refine ⟨?_,?_,hr,hc⟩
  · intro v hv u;simp [J',ordinaryRootColumnRepair,hv]
  · intro u hu v;simp [J',ordinaryRootColumnRepair,hu]
end Oberwolfach
