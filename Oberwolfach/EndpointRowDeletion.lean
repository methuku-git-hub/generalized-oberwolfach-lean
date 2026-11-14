module

public import Oberwolfach.FinitePredicateLoss
public import Oberwolfach.EndpointPotentialLoads

@[expose] public section

/-! Realised rim and spoke deletions in the endpoint row potential.
The tested root rim edge is absent from the predicate on both sides. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

theorem endpoint_row_predicate_sdiff (P R H F D E:SimpleGraph V) (A B:Finset V)
    (x v:V) (p:V×V) :
    EndpointRowPotentialPredicate P (R\D) (H\E) F A B x v p ↔
      EndpointRowPotentialPredicate P R H F A B x v p ∧
      ¬D.Adj x p.2 ∧ ¬D.Adj v p.2 ∧ ¬E.Adj x p.1 ∧ ¬E.Adj v p.1 ∧ ¬E.Adj p.2 p.1 := by
  simp only [EndpointRowPotentialPredicate,SimpleGraph.sdiff_adj]
  tauto

theorem endpoint_row_removed_count (P R H F D E:SimpleGraph V) (A B:Finset V)
    (x v:V) (L:ℝ) (hE:∀ u∈B,(E.degree u:ℝ)≤L) :
    ((Finset.univ.filter (fun p:V×V=>EndpointRowPotentialPredicate P R H F A B x v p ∧
      ¬EndpointRowPotentialPredicate P (R\D) (H\E) F A B x v p)).card:ℝ)≤
      B.card*((D.degree x:ℝ)+D.degree v+L)+A.card*((E.degree x:ℝ)+E.degree v) := by
  let U₁:=B.product (A∩D.neighborFinset x)
  let U₂:=B.product (A∩D.neighborFinset v)
  let U₃:=(B∩E.neighborFinset x).product A
  let U₄:=(B∩E.neighborFinset v).product A
  let U₅:=B.biUnion (fun u=>({u}:Finset V).product (A∩E.neighborFinset u))
  have hsubset:Finset.univ.filter (fun p:V×V=>EndpointRowPotentialPredicate P R H F A B x v p ∧
      ¬EndpointRowPotentialPredicate P (R\D) (H\E) F A B x v p)⊆U₁∪U₂∪U₃∪U₄∪U₅:=by
    intro p hp
    obtain ⟨hp,hno⟩:=(Finset.mem_filter.mp hp).2
    have hw:p.2∈A:=(Finset.mem_inter.mp hp.2.1.2.1).1
    have hbad:D.Adj x p.2∨D.Adj v p.2∨E.Adj x p.1∨E.Adj v p.1∨E.Adj p.2 p.1:=by
      rw [endpoint_row_predicate_sdiff] at hno
      tauto
    simp only [Finset.mem_union]
    rcases hbad with hd|hd|he|he|he
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_product.mpr ⟨hp.1,Finset.mem_inter.mpr ⟨hw,by simpa using hd⟩⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_product.mpr ⟨hp.1,Finset.mem_inter.mpr ⟨hw,by simpa using hd⟩⟩))))
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hp.1,by simpa using he⟩,hw⟩)))
    · exact Or.inl (Or.inr (Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hp.1,by simpa using he⟩,hw⟩))
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨p.1,hp.1,Finset.mem_product.mpr
        ⟨Finset.mem_singleton_self _,Finset.mem_inter.mpr ⟨hw,by simpa using he.symm⟩⟩⟩)
  have h₁:(U₁.card:ℝ)≤B.card*D.degree x:=by
    dsimp [U₁];rw [Finset.card_product,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) (Nat.cast_nonneg _)
  have h₂:(U₂.card:ℝ)≤B.card*D.degree v:=by
    dsimp [U₂];rw [Finset.card_product,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) (Nat.cast_nonneg _)
  have h₃:(U₃.card:ℝ)≤E.degree x*A.card:=by
    dsimp [U₃];rw [Finset.card_product,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) (Nat.cast_nonneg _)
  have h₄:(U₄.card:ℝ)≤E.degree v*A.card:=by
    dsimp [U₄];rw [Finset.card_product,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) (Nat.cast_nonneg _)
  have h₅:(U₅.card:ℝ)≤B.card*L:=by
    have hh:U₅.card≤∑ u∈B,(A∩E.neighborFinset u).card:=by
      exact (Finset.card_biUnion_le).trans_eq (by simp)
    calc
      _ ≤ ∑ u∈B,((A∩E.neighborFinset u).card:ℝ):=by exact_mod_cast hh
      _ ≤ ∑ u∈B,L:=Finset.sum_le_sum (fun u hu=>(Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans (hE u hu))
      _ = _:=by simp
  have hu:(U₁∪U₂∪U₃∪U₄∪U₅).card≤U₁.card+U₂.card+U₃.card+U₄.card+U₅.card:=by
    have h12:=Finset.card_union_le U₁ U₂
    have h123:=Finset.card_union_le (U₁∪U₂) U₃
    have h1234:=Finset.card_union_le (U₁∪U₂∪U₃) U₄
    have h12345:=Finset.card_union_le (U₁∪U₂∪U₃∪U₄) U₅
    omega
  have hc:( (Finset.univ.filter (fun p:V×V=>EndpointRowPotentialPredicate P R H F A B x v p ∧
      ¬EndpointRowPotentialPredicate P (R\D) (H\E) F A B x v p)).card:ℝ)≤
      U₁.card+U₂.card+U₃.card+U₄.card+U₅.card:=by exact_mod_cast (Finset.card_le_card hsubset).trans hu
  nlinarith only [hc,h₁,h₂,h₃,h₄,h₅]

theorem endpoint_row_potential_deletion (P R H F D E:SimpleGraph V) (A B:Finset V)
    (x v:V) (weight:Sym2 V→ℝ) (d M L:ℝ) (hM:0≤M)
    (hw:∀ w,(endpointEligibleGraph P F (A∩P.neighborFinset x) x).Adj v w →
      0≤weight s(v,w)/d∧weight s(v,w)/d≤M)
    (hE:∀ u∈B,(E.degree u:ℝ)≤L) :
    0≤endpointRowPotential P R H F A B x v weight d-endpointRowPotential P (R\D) (H\E) F A B x v weight d ∧
    |endpointRowPotential P (R\D) (H\E) F A B x v weight d-endpointRowPotential P R H F A B x v weight d|≤
      M*(B.card*((D.degree x:ℝ)+D.degree v+L)+A.card*((E.degree x:ℝ)+E.degree v)) := by
  have hh:=finite_predicate_loss (EndpointRowPotentialPredicate P R H F A B x v)
    (EndpointRowPotentialPredicate P (R\D) (H\E) F A B x v) (fun p=>weight s(v,p.2)/d) M
    (fun p hp=>((endpoint_row_predicate_sdiff P R H F D E A B x v p).mp hp).1)
    (fun p hp=>hw p.2 hp.2.1)
  change 0≤endpointRowPotential P R H F A B x v weight d-endpointRowPotential P (R\D) (H\E) F A B x v weight d ∧ _ at hh
  refine ⟨hh.1,?_⟩
  rw [abs_sub_comm,abs_of_nonneg hh.1]
  exact hh.2.trans (mul_le_mul_of_nonneg_left (endpoint_row_removed_count P R H F D E A B x v L hE) hM)

end Oberwolfach
