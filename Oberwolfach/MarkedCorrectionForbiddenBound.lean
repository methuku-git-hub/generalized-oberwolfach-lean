module

public import Oberwolfach.MarkedCorrectionFromCandidateBounds

@[expose] public section
/-! For a fixed head, the physical unordered pair determines the directed
arc. Thus excluding a finite set of physical rim pairs removes at most one
incoming arc per pair. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [Nonempty V]
variable (P:V×V→Prop)
local instance candidateArcDecEq2 : DecidableEq {e:V×V // P e} := fun a b => Classical.propDecidable (a=b)

theorem marked_correction_forbidden_incoming_bound
    (C:Finset (Finset V)) (v:V):
    ((Finset.univ.filter (fun e:{a:V×V // P a}=>e.val.2=v ∧
      ({e.val.1,e.val.2}:Finset V)∈C)).card:ℝ)≤C.card :=by
  let F:=Finset.univ.filter (fun e:{a:V×V // P a}=>e.val.2=v ∧
    ({e.val.1,e.val.2}:Finset V)∈C)
  have hinj: Set.InjOn (fun e:{a:V×V // P a}=>({e.val.1,e.val.2}:Finset V)) F :=by
    intro a ha b hb hab
    change ({a.val.1,a.val.2}:Finset V)=({b.val.1,b.val.2}:Finset V) at hab
    have hA:=(Finset.mem_filter.mp ha).2
    have hB:=(Finset.mem_filter.mp hb).2
    have hm:a.val.1∈({b.val.1,v}:Finset V):=by
      rw [←hB.1,←hab]
      simp
    have hn:b.val.1∈({a.val.1,v}:Finset V):=by
      rw [←hA.1,hab]
      simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm hn
    have ht:a.val.1=b.val.1:=by
      rcases hm with h|h
      · exact h
      · rcases hn with h'|h'
        · exact h'.symm
        · exact h.trans h'.symm
    apply Subtype.ext
    exact Prod.ext ht (hA.1.trans hB.1.symm)
  have hcard:(F.image (fun e=>({e.val.1,e.val.2}:Finset V))).card=F.card:=Finset.card_image_iff.mpr hinj
  have hsub:F.image (fun e=>({e.val.1,e.val.2}:Finset V))⊆C:=by
    intro x hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ha).2.2
  have h:=Finset.card_le_card hsub
  rw [hcard] at h
  exact_mod_cast h

/-- The correction with the forbidden family chosen from the reserved
physical rim pairs, with its incoming loss bounded by the number of pairs. -/
theorem marked_correction_with_reserved_pair_count
    (S₀ S₁ T₀ T₁ B₀ B₁:Finset {e:V×V // P e})
    (C:Finset (Finset V)) (b:ℕ) (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hdis:Disjoint T₀ T₁) (h₀:S₀\T₀⊆B₀) (h₁:S₁\T₁⊆B₁)
    (hdev:∀ v, |(directedInCount P T₁ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (base₀ base₁ loss₀ loss₁:V→ℝ)
    (hbase₀:∀ v, base₀ v≤(S₀.filter (fun e=>e.val.2=v)).card)
    (hbase₁:∀ v, base₁ v≤(S₁.filter (fun e=>e.val.2=v)).card)
    (hloss₀:∀ v, ((B₀.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₀ v)
    (hloss₁:∀ v, ((B₁.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₁ v)
    (hmargin₀:∀ v, rho*Fintype.card V≤base₀ v-loss₀ v-C.card)
    (hmargin₁:∀ v, rho*Fintype.card V≤base₁ v-loss₁ v-C.card):
    let F:=Finset.univ.filter (fun e:{a:V×V // P a}=>({e.val.1,e.val.2}:Finset V)∈C)
    let A:=(T₀∪T₁)\F
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M T₁⊆A ∧
      (∀ e, ({e.val.1,e.val.2}:Finset V)∈C → (e∈M ↔ e∈T₁)) ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  intro F A
  have hprotect:∀ e:{a:V×V // P a}, ({e.val.1,e.val.2}:Finset V)∈C → e∈F:=by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
  have hforbid:∀ v, ((F.filter (fun e=>e.val.2=v)).card:ℝ)≤C.card:=by
    intro v
    have heq:F.filter (fun e=>e.val.2=v)=Finset.univ.filter
        (fun e:{a:V×V // P a}=>e.val.2=v ∧ ({e.val.1,e.val.2}:Finset V)∈C):=by
      ext e
      simp [F, and_comm]
    rw [heq]
    exact marked_correction_forbidden_incoming_bound P C v
  exact marked_correction_from_candidate_bounds (P:=P) S₀ S₁ T₀ T₁ B₀ B₁ F C b rho eta hrho heta hetaR
    hdis h₀ h₁ hprotect hdev base₀ base₁ loss₀ loss₁ (fun _=>C.card)
    hbase₀ hbase₁ hloss₀ hloss₁ hforbid hmargin₀ hmargin₁
end Oberwolfach
