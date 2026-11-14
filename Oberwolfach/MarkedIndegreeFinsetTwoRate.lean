module

public import Oberwolfach.MarkedIndegreeFinsetInterface
public import Oberwolfach.MarkedRetypedPhysicalDegreeTwoRate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [Nonempty V]
local instance candidateLocalArcDecEqMarkedIndegreeFinsetTwoRate (P:V×V→Prop):DecidableEq {e:V×V // P e}:=fun a b=>Classical.propDecidable (a=b)

theorem marked_indegree_correction_finsets_two_rate
    (P:V×V→Prop) (M₀ A:Finset {e:V×V // P e}) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (I:Finset V) (loc inside:ℝ) (hloc:0≤loc) (hinside:0≤ inside)
    (hlocGlobal:loc≤eta*Fintype.card V) (hinsideGlobal:inside≤eta*Fintype.card V)
    (hdevinside:∀v,v∈I→|(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤ inside)
    (hdevlocal:∀v,v∉I→|(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤loc)
    (hdev:∀ v, |(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A∩M₀) v:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A\M₀) v:ℝ)) :
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M M₀⊆A ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M M₀)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+1) ∧
      (∀v,v∉I→((physicalEdgeGraph (changedDirectedPhysicalEdges P M M₀)).degree v:ℝ)≤
        loc+((I.card:ℝ)*inside/Fintype.card V+loc)/rho+1) := by
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
  have hlocal':∀v,v∉I→|(markedHeadCount (fun e:{e:V×V // P e}=>e.val.2) B₀ v:ℝ)-(b:ℝ)|≤loc:=by
    intro v hv;rw [hcount];exact hdevlocal v hv
  obtain ⟨B,hB,hA,hdeg,hlocal⟩ := marked_indegree_correction_physical_two_rate
    (fun e:{e:V×V // P e}=>e.val.1) (fun e=>e.val.2) B₀ (fun e=>e∈A) b rho eta
    hrho heta hetaR I loc inside hloc hinside hlocGlobal hinsideGlobal (by intro v hv; rw [hcount]; exact hdevinside v hv) hlocal' (by intro e f h;apply Subtype.ext;exact h) hdev' hm hu
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
  refine ⟨M,?_,?_,?_,?_⟩
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
  · intro v hv
    rw [hedges]
    exact hlocal v hv
theorem marked_indegree_correction_protect_reserved_two_rate
    (P:V×V→Prop) (M₀ A:Finset {e:V×V // P e}) (C:Finset (Finset V))
    (b:ℕ) (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (I:Finset V) (loc inside:ℝ) (hloc:0≤loc) (hinside:0≤ inside)
    (hlocGlobal:loc≤eta*Fintype.card V) (hinsideGlobal:inside≤eta*Fintype.card V)
    (hdevinside:∀v,v∈I→|(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤ inside)
    (hdevlocal:∀v,v∉I→|(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤loc)
    (hdev:∀ v, |(directedInCount P M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A∩M₀) v:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(directedInCount P (A\M₀) v:ℝ))
    (hprotect:∀ e∈A, ({e.val.1,e.val.2}:Finset V)∉C) :
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M M₀⊆A ∧
      (∀ e, ({e.val.1,e.val.2}:Finset V)∈C → (e∈M ↔ e∈M₀)) ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M M₀)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+1) ∧
      (∀v,v∉I→((physicalEdgeGraph (changedDirectedPhysicalEdges P M M₀)).degree v:ℝ)≤
        loc+((I.card:ℝ)*inside/Fintype.card V+loc)/rho+1) := by
  obtain ⟨M,hdeg,hchange,hbound,hlocal⟩ := marked_indegree_correction_finsets_two_rate P M₀ A b rho eta
    hrho heta hetaR I loc inside hloc hinside hlocGlobal hinsideGlobal hdevinside hdevlocal hdev hmarked hunmarked
  refine ⟨M,hdeg,hchange,?_,hbound,hlocal⟩
  intro e he
  by_contra hn
  have hs : e∈symmDiff M M₀ := by
    rw [Finset.mem_symmDiff]
    tauto
  exact (hprotect e (hchange hs)) he
end Oberwolfach
