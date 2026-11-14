module

public import Oberwolfach.InducedBoundedDeletionDegrees

@[expose] public section
/-! Numerical conditions for applying the almost-regular factor theorem
after removing a bounded set and a graph of maximum degree two. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem induced_bounded_factor_inputs {V:Type} [Fintype V] [DecidableEq V]
    (G Dgraph:SimpleGraph V) (S A:Finset V) (D δ α η ε:ℝ) (b:ℕ)
    (hδ:(1/2:ℝ)≤δ) (hα:0<α) (hε:0<ε)
    (hAS:A⊆S) (hbound:(S\A).card≤b) (hsize:S.card≤2*A.card)
    (hDlo:(δ+α)*S.card≤D) (hDhi:D≤S.card)
    (hnear:∀ v,|((G.neighborFinset v∩S).card:ℝ)-D|≤η*S.card)
    (hD:∀ v,Dgraph.degree v≤2)
    (herrα:η*S.card+b+2≤(α/2)*S.card)
    (herrε:η*S.card+b+2≤ε*A.card):
    let Q:=triangleAugmentationGraph G Dgraph A;
    let P:=Q.induce (A:Set V);
    (Fintype.card (A:Set V):ℝ)/2≤D ∧ D≤2*Fintype.card (A:Set V) ∧
    (∀ v,(δ+α/8)*Fintype.card (A:Set V)≤(P.degree v:ℝ)) ∧
    (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card (A:Set V)):=by
  intro Q P
  have hA:(A.card:ℝ)≤S.card:=by exact_mod_cast Finset.card_le_card hAS
  have hsizeR:(S.card:ℝ)≤2*A.card:=by exact_mod_cast hsize
  have hA0:(0:ℝ)≤A.card:=by positivity
  have hS0:(0:ℝ)≤S.card:=by positivity
  have hAcard:Fintype.card (A:Set V)=A.card:=Fintype.card_coe A
  refine ⟨?_,?_,?_,?_⟩
  · rw [hAcard];nlinarith
  · rw [hAcard];nlinarith
  · intro v
    have hh:=abs_le.mp (induced_bounded_deletion_degrees G Dgraph S A D η b hAS hbound hnear hD v)
    have hcoeff:0≤δ+α/8:=by linarith
    have hprod:=mul_le_mul_of_nonneg_left hA hcoeff
    rw [hAcard]
    change (δ+α/8)*A.card≤((triangleAugmentationGraph G Dgraph A).induce (A:Set V)).degree v
    nlinarith
  · intro v
    rw [hAcard]
    exact (induced_bounded_deletion_degrees G Dgraph S A D η b hAS hbound hnear hD v).trans herrε
end Oberwolfach
