module

public import Oberwolfach.RetypedPhysicalDegree

@[expose] public section
/-! Finite-set form of the marked-indegree correction. The arc universe is a
subtype of ordered vertex pairs, and the physical change graph is built from
the symmetric difference of the old and new marked sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [Nonempty V]

def directedInCount (P:V×V→Prop) (M:Finset {e:V×V // P e}) (v:V) : ℕ :=
  (M.filter (fun e=>e.val.2=v)).card

def changedDirectedPhysicalEdges (P:V×V→Prop)
    (M M₀:Finset {e:V×V // P e}) : Finset (Finset V) :=
  (symmDiff M M₀).image (fun e=>({e.val.1,e.val.2}:Finset V))

theorem marked_indegree_correction_finsets
    (P:V×V→Prop) (M₀ A:Finset {e:V×V // P e}) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hdev:∀ v, |(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A∩M₀) v:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A\M₀) v:ℝ)) :
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M M₀⊆A ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M M₀)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  let B₀ : {e:V×V // P e}→Bool := fun e=>decide (e∈M₀)
  have hcount : ∀ v, markedHeadCount (fun e:{e:V×V // P e}=>e.val.2) B₀ v = directedInCount P M₀ v := by
    intro v
    have heq : Finset.univ.filter (fun e:{e:V×V // P e}=>e.val.2=v ∧ B₀ e=true) =
        M₀.filter (fun e=>e.val.2=v) := by
      ext e
      simp [B₀, and_comm]
    unfold markedHeadCount directedInCount
    rw [← Finset.card_filter,heq]
  have hflex : ∀ v flag,
      markedFlexibleIncoming (fun e:{e:V×V // P e}=>e.val.2) B₀ (fun e=>e∈A) v flag =
      directedInCount P (if flag then A∩M₀ else A\M₀) v := by
    intro v flag
    unfold markedFlexibleIncoming directedInCount
    congr 1
    ext e
    cases flag <;> simp [B₀,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_inter, and_assoc, and_comm, and_left_comm]
  have hdev' : ∀v, |(markedHeadCount (fun e:{e:V×V // P e}=>e.val.2) B₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V := by
    intro v; rw [hcount]; exact hdev v
  have hm : ∀v, rho*Fintype.card V≤(markedFlexibleIncoming (fun e:{e:V×V // P e}=>e.val.2) B₀ (fun e=>e∈A) v true:ℝ) := by
    intro v; rw [hflex]; exact hmarked v
  have hu : ∀v, rho*Fintype.card V≤(markedFlexibleIncoming (fun e:{e:V×V // P e}=>e.val.2) B₀ (fun e=>e∈A) v false:ℝ) := by
    intro v; rw [hflex]; exact hunmarked v
  obtain ⟨B,hB,hA,hdeg⟩ := marked_indegree_correction_oriented_graph P B₀ (fun e=>e∈A) b rho eta
    hrho heta hetaR hdev' hm hu
  let M : Finset {e:V×V // P e} := Finset.univ.filter (fun e=>B e=true)
  have hmem : ∀ e, e∈M ↔ B e=true := by intro e; simp [M]
  have hchange : ∀ e, e∈symmDiff M M₀ ↔ B e≠B₀ e := by
    intro e
    rw [Finset.mem_symmDiff]
    simp only [hmem,B₀,decide_eq_true_eq]
    by_cases he:e∈M₀ <;> cases hb:B e <;> simp [he,hb]
  have hedges : changedDirectedPhysicalEdges P M M₀ =
      retypedPhysicalEdges (fun e:{e:V×V // P e}=>e.val.1) (fun e=>e.val.2) B B₀ := by
    unfold changedDirectedPhysicalEdges retypedPhysicalEdges
    congr 1
    ext e
    simp only [Finset.mem_symmDiff,Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [Finset.mem_symmDiff] using hchange e
  refine ⟨M,?_,?_,?_⟩
  · intro v
    have hc : directedInCount P M v = markedHeadCount (fun e:{e:V×V // P e}=>e.val.2) B v := by
      have heq : Finset.univ.filter (fun e:{e:V×V // P e}=>e.val.2=v ∧ B e=true) =
          M.filter (fun e=>e.val.2=v) := by
        ext e
        simp [hmem e, and_comm]
      unfold directedInCount markedHeadCount
      rw [← Finset.card_filter,heq]
    rw [hc]; exact hB v
  · intro e he
    exact hA e ((hchange e).mp he)
  · intro v
    rw [hedges]
    exact hdeg v
theorem marked_indegree_correction_protect_reserved
    (P:V×V→Prop) (M₀ A:Finset {e:V×V // P e}) (C:Finset (Finset V))
    (b:ℕ) (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hdev:∀ v, |(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A∩M₀) v:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A\M₀) v:ℝ))
    (hprotect:∀ e∈A, ({e.val.1,e.val.2}:Finset V)∉C) :
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M M₀⊆A ∧
      (∀ e, ({e.val.1,e.val.2}:Finset V)∈C → (e∈M ↔ e∈M₀)) ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M M₀)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  obtain ⟨M,hdeg,hchange,hbound⟩ := marked_indegree_correction_finsets P M₀ A b rho eta
    hrho heta hetaR hdev hmarked hunmarked
  refine ⟨M,hdeg,hchange,?_,hbound⟩
  intro e he
  by_contra hn
  have hs : e∈symmDiff M M₀ := by
    rw [Finset.mem_symmDiff]
    tauto
  exact (hprotect e (hchange hs)) he
end Oberwolfach
