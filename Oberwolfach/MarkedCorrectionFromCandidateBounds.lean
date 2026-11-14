module

public import Oberwolfach.IncomingCandidateLoss
public import Oberwolfach.MarkedIndegreeFinsetInterface

@[expose] public section
/-! Combine the deterministic incoming-candidate loss estimates with the
marked-indegree correction, while protecting reserved physical edges. The
caller must still establish the concrete source-set and loss bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [Nonempty V]
variable (P:V×V→Prop)
local instance candidateArcDecEq : DecidableEq {e:V×V // P e} := fun a b => Classical.propDecidable (a=b)

theorem marked_correction_from_candidate_bounds
    (S₀ S₁ T₀ T₁ B₀ B₁ F:Finset {e:V×V // P e}) (C:Finset (Finset V))
    (b:ℕ) (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hdis:Disjoint T₀ T₁) (h₀:S₀\T₀⊆B₀) (h₁:S₁\T₁⊆B₁)
    (hprotected:∀ e, ({e.val.1,e.val.2}:Finset V)∈C → e∈F)
    (hdev:∀ v, |(directedInCount P T₁ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (base₀ base₁ loss₀ loss₁ forbid:V→ℝ)
    (hbase₀:∀ v, base₀ v≤(S₀.filter (fun e=>e.val.2=v)).card)
    (hbase₁:∀ v, base₁ v≤(S₁.filter (fun e=>e.val.2=v)).card)
    (hloss₀:∀ v, ((B₀.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₀ v)
    (hloss₁:∀ v, ((B₁.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₁ v)
    (hforbid:∀ v, ((F.filter (fun e=>e.val.2=v)).card:ℝ)≤forbid v)
    (hmargin₀:∀ v, rho*Fintype.card V≤base₀ v-loss₀ v-forbid v)
    (hmargin₁:∀ v, rho*Fintype.card V≤base₁ v-loss₁ v-forbid v) :
    let A:=(T₀∪T₁)\F
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M T₁⊆A ∧
      (∀ e, ({e.val.1,e.val.2}:Finset V)∈C → (e∈M ↔ e∈T₁)) ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  intro A
  have hflex : ∀ v,
      rho*Fintype.card V≤(directedInCount P (A∩T₁) v:ℝ) ∧
      rho*Fintype.card V≤(directedInCount P (A\T₁) v:ℝ) := by
    intro v
    exact incoming_flexible_availability_real (fun e:{e:V×V // P e}=>e.val.2)
      S₀ S₁ T₀ T₁ B₀ B₁ F v hdis h₀ h₁ (base₀ v) (base₁ v) (loss₀ v) (loss₁ v)
      (forbid v) (rho*Fintype.card V) (hbase₀ v) (hbase₁ v) (hloss₀ v) (hloss₁ v)
      (hforbid v) (hmargin₀ v) (hmargin₁ v)
  have hprotect : ∀ e∈A, ({e.val.1,e.val.2}:Finset V)∉C := by
    intro e he hC
    exact (Finset.mem_sdiff.mp he).2 (hprotected e hC)
  have hm : ∀ v, rho*Fintype.card V≤(directedInCount P (A∩T₁) v:ℝ) := fun v=>(hflex v).1
  have hu : ∀ v, rho*Fintype.card V≤(directedInCount P (A\T₁) v:ℝ) := fun v=>(hflex v).2
  letI : DecidableEq {e:V×V // P e} := Subtype.instDecidableEq
  have hm' : ∀ v, rho*Fintype.card V≤(directedInCount P (A∩T₁) v:ℝ) := by
    intro v
    convert hm v using 1 <;> congr 2 <;> ext e <;> simp
  have hu' : ∀ v, rho*Fintype.card V≤(directedInCount P (A\T₁) v:ℝ) := by
    intro v
    convert hu v using 1 <;> congr 2 <;> ext e <;> simp
  obtain ⟨M,hM,hA,hC,hB⟩ := marked_indegree_correction_protect_reserved P T₁ A C b rho eta
    hrho heta hetaR hdev hm' hu' hprotect
  refine ⟨M,hM,?_,hC,hB⟩
  intro e he
  apply hA
  simpa only [Finset.mem_symmDiff] using he
end Oberwolfach
