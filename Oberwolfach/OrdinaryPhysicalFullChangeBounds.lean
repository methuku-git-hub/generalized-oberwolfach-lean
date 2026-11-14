module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.EmbeddedClassChanges

@[expose] public section
/-! The original full rim and spoke row/column edit budgets are exactly the
corresponding physical-sum neighborhood budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_full_change_bounds (R Q:SimpleGraph V) (H J:V→U→Prop) (L:ℝ) (hL:0≤L)
    (hr:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    (∀z:V⊕U,((changed ((ordinaryPhysicalGraph R (fun _ _=>False)).neighborFinset z)
      ((ordinaryPhysicalGraph Q (fun _ _=>False)).neighborFinset z)).card:ℝ)≤L) ∧
    (∀z:V⊕U,((changed ((ordinaryPhysicalGraph ⊥ H).neighborFinset z)
      ((ordinaryPhysicalGraph ⊥ J).neighborFinset z)).card:ℝ)≤L):=by
  have hrim (G:SimpleGraph V) (v:V):
      (ordinaryPhysicalGraph G (fun _ _=>False)).neighborFinset (Sum.inl v:V⊕U)=
      (G.neighborFinset v).image (Sum.inl:V→V⊕U):=by
    ext z
    cases z <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
  have hroweq (K:V→U→Prop) (v:V):
      (ordinaryPhysicalGraph ⊥ K).neighborFinset (Sum.inl v)=
      (Finset.univ.filter (K v)).image Sum.inr:=by
    ext z
    cases z <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
  have hcoleq (K:V→U→Prop) (u:U):
      (ordinaryPhysicalGraph ⊥ K).neighborFinset (Sum.inr u)=
      (Finset.univ.filter (fun v=>K v u)).image Sum.inl:=by
    ext z
    cases z <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
  constructor
  · intro z
    cases z with
    | inl v=>
      rw [hrim R v,hrim Q v,changed_image_card _ Sum.inl_injective]
      exact hr v
    | inr u=>
      have he (G:SimpleGraph V):(ordinaryPhysicalGraph G (fun _ _=>False)).neighborFinset (Sum.inr u)=∅:=by
        ext z
        cases z <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
      rw [he R,he Q]
      simpa [changed] using hL
  · intro z
    cases z with
    | inl v=>
      rw [hroweq H v,hroweq J v,changed_image_card _ Sum.inr_injective]
      exact hrow v
    | inr u=>
      rw [hcoleq H u,hcoleq J u,changed_image_card _ Sum.inl_injective]
      exact hcol u
end Oberwolfach
