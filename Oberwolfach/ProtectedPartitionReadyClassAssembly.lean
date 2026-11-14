module

public import Oberwolfach.ProtectedPartitionGraphEventsSameColour

@[expose] public section
/-! Feed the protected graphs provided by the preparation events into the
partition event on the same colouring, then use their robust conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_partition_ready_class_assembly {n k:ℕ}
    (G:SimpleGraph (Fin n)) (c:Sym2 (Fin n)→Fin k)
    (m:Fin k→ℕ) (F:∀a,Fin (m a)→SimpleGraph (Fin n))
    (I:Fin k→Finset (Fin n)) (ξ:ℝ) (B:ℕ) (Ba:Fin k→ℕ)
    (hB:∑a,Ba a≤B)
    (hReady:∀a,∃A:SimpleGraph (Fin n),A≤edgeColourGraph G c a ∧ A.edgeFinset.card≤Ba a ∧
      ∀H:SimpleGraph (Fin n),H≤G→H.IsRegularOfDegree (2*m a)→A≤H→
        (∀x∈I a,∀y∈I a,H.Adj x y↔(edgeColourGraph G c a).Adj x y)→
        (∀x,((Finset.univ.filter (fun y=>Xor (H.Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n)→
        HasFactorDecomposition H (F a))
    (hPartition:∀A:Fin k→SimpleGraph (Fin n),
      (∀a,A a≤edgeColourGraph G c a)→(∑a,(A a).edgeFinset.card)≤B→
      ∃H:Fin k→SimpleGraph (Fin n),
        EdgePartition G H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
        (∀a,A a≤H a) ∧
        (∀a b x,x∈I b→∀y,y∈I b→((H a).Adj x y↔(edgeColourGraph G c a).Adj x y)) ∧
        (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n)):
    ∃H:Fin k→SimpleGraph (Fin n),EdgePartition G H ∧ ∀a,HasFactorDecomposition (H a) (F a) :=by
  choose A hAle hAcard hRobust using hReady
  have hsum:(∑a,(A a).edgeFinset.card)≤B:=(Finset.sum_le_sum (fun a _=>hAcard a)).trans hB
  obtain ⟨H,hpart,hreg,hprotect,hinside,hdiff⟩:=hPartition A hAle hsum
  have hHsub:∀a,H a≤G:=by
    intro a x y hxy
    exact ((hpart x y).1).mpr ⟨a,hxy⟩
  refine ⟨H,hpart,?_⟩
  intro a
  exact hRobust a (H a) (hHsub a) (hreg a) (hprotect a) (fun x hx y hy=>hinside a a x hx y hy) (hdiff a)
end Oberwolfach
