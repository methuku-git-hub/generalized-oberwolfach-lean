module

public import Oberwolfach.MarkedFiniteDeletionDegrees
public import Oberwolfach.MarkedPhysicalRimDeletionDegrees

@[expose] public section

/-! An actual physical rim degree bound controls the auxiliary incidence
count of any finite set of sampled typed arcs. Incoming marked arcs are
charged at the successor of their auxiliary head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_finite_physical_incidence_bound
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    ∀ (A:Finset (E₀⊕E₁)) (δ:ℝ),
    (∀ x,((markedSampleArcSetGraph P π d σ A).degree x:ℝ)≤δ)→∀ v,
    ((A.filter (fun a=>Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a=v∨
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a=v)).card:ℝ)≤4*δ:=by
  intro E₀ E₁ A δ hD v
  let D:=markedSampleArcSetGraph P π d σ A
  have hAdj0 (a:E₀) (ha:Sum.inl a∈A):D.Adj a.val.1 a.val.2:=by
    have h:=(markedSampleArcSetGraph_coordinate P π d σ A (Sum.inl a)).mpr ha
    simpa only [Sum.elim_inl,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using h
  have hAdj1 (a:E₁) (ha:Sum.inr a∈A):D.Adj a.val.1 (π a.val.2):=by
    have h:=(markedSampleArcSetGraph_coordinate P π d σ A (Sum.inr a)).mpr ha
    simpa only [Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using h
  obtain ⟨h0,h1,h2,h3⟩:=marked_physical_rim_deletion_degrees
    (fun e:E₀=>e.val.1) (fun e:E₀=>e.val.2) (fun e:E₁=>e.val.1) (fun e:E₁=>e.val.2) π
    (markedSampleArc_physical_injective P π (3*d) _) D δ hD
  have hset:(A.filter (fun a=>Sum.elim (fun e:E₀=>e.val.1) (fun e:E₁=>e.val.1) a=v∨
      Sum.elim (fun e:E₀=>e.val.2) (fun e:E₁=>e.val.2) a=v))=
      Finset.univ.filter (fun a:E₀⊕E₁=>a∈A∧(Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a=v∨
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a=v)):=by
    ext a;simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hset,←Finset.sum_boole,Fintype.sum_sum_type]
  have hE:(∑ a:E₀,if Sum.inl a∈A∧(a.val.1=v∨a.val.2=v) then (1:ℝ) else 0)≤2*δ:=by
    calc
      _ ≤ ∑ a:E₀,((if D.Adj a.val.1 a.val.2∧a.val.1=v then (1:ℝ) else 0)+
        (if D.Adj a.val.1 a.val.2∧a.val.2=v then 1 else 0)):=by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha:Sum.inl a∈A
        · have hd:=hAdj0 a ha
          by_cases ht:a.val.1=v <;> by_cases hh:a.val.2=v <;> simp_all
        · simp only [ha,false_and,ite_false];positivity
      _ ≤ 2*δ:=by rw [Finset.sum_add_distrib];linarith only [h0 v,h1 v]
  have hK:(∑ a:E₁,if Sum.inr a∈A∧(a.val.1=v∨a.val.2=v) then (1:ℝ) else 0)≤2*δ:=by
    calc
      _ ≤ ∑ a:E₁,((if D.Adj a.val.1 (π a.val.2)∧a.val.1=v then (1:ℝ) else 0)+
        (if D.Adj a.val.1 (π a.val.2)∧a.val.2=v then 1 else 0)):=by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha:Sum.inr a∈A
        · have hd:=hAdj1 a ha
          by_cases ht:a.val.1=v <;> by_cases hh:a.val.2=v <;> simp_all
        · simp only [ha,false_and,ite_false];positivity
      _ ≤ 2*δ:=by rw [Finset.sum_add_distrib];linarith only [h2 v,h3 v]
  simp only [Sum.elim_inl,Sum.elim_inr]
  linarith only [hE,hK]

end Oberwolfach
