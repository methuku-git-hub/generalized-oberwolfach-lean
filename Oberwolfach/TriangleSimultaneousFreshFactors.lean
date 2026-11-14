module

public import Oberwolfach.TriangleTransformerAvailableFactors
public import Oberwolfach.FiniteFreshSets

@[expose] public section
/-! The triangular transformer can choose all its boundedly many new sets
sequentially, with a single threshold fixed before the host. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def TriangleTransformerFactorPair {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (S Z:Finset V):Prop:=
  ∃ M₁ M₂:Finset (OrdinaryCycle G 3),
    (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
    M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z ∧
    (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
    M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
    (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
    (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S)

theorem triangle_transformer_simultaneous_fresh_factors
    (K L:ℕ) (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s→3∣s→∃ N:ℕ,
    ∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J],
    N≤Fintype.card V→Fintype.card J≤K→
    ∀ (G:SimpleGraph V) (A Z:J→Finset V),
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ)) →
    (∀ i,(Z i).card≤L ∧ 3∣(Z i).card) →
    (∀ i,(((Finset.univ:Finset V)\A i).card:ℝ)≤(β/4)*(Fintype.card V:ℝ)) →
    ∃ S:J→Finset V,
      (∀ i,(S i).card=s ∧ S i⊆A i ∧ Disjoint (S i) (Z i) ∧ TriangleTransformerFactorPair G (S i) (Z i)) ∧
      (∀ i j,i≠j→Disjoint (S i) (S j)) :=by
  obtain ⟨s₀,hs⟩:=triangle_transformer_available_sample_factors L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hsdiv
  obtain ⟨N₀,hN₀⟩:=hs s hs₀ hsdiv
  obtain ⟨M,hM⟩:=exists_nat_gt (4*(K*s:ℝ)/β)
  refine ⟨max N₀ M,?_⟩
  intro V J _ _ _ _ hn hJ G A Z hdeg hZ hmiss
  have hn₀:N₀≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnM:(M:ℝ)≤Fintype.card V:=Nat.cast_le.mpr ((le_max_right _ _).trans hn)
  have hbudget:(K*s:ℝ)≤(β/4)*(Fintype.card V:ℝ):=by
    have hm:4*(K*s:ℝ)<(M:ℝ)*β:=(div_lt_iff₀ hβ).mp hM
    nlinarith
  let P:J→Finset V→Prop:=fun i S=>S⊆A i ∧ Disjoint S (Z i) ∧ TriangleTransformerFactorPair G S (Z i)
  have hchoose:∀ i (B:Finset V),B.card≤Fintype.card J*s →
      ∃ S:Finset V,S.card=s ∧ P i S ∧ Disjoint S B:=by
    intro i B hB
    have hB':(B.card:ℝ)≤(K*s:ℝ):=by exact_mod_cast hB.trans (Nat.mul_le_mul_right s hJ)
    have hsub:(Finset.univ:Finset V)\(A i\B) ⊆ ((Finset.univ:Finset V)\A i)∪B:=by
      intro x hx
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union] at hx ⊢
      tauto
    have hcard:(((Finset.univ:Finset V)\(A i\B)).card:ℝ)≤
        (((Finset.univ:Finset V)\A i).card:ℝ)+(B.card:ℝ):=by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hmiss':(((Finset.univ:Finset V)\(A i\B)).card:ℝ)≤(β/2)*(Fintype.card V:ℝ):=by
      have hi:=hmiss i
      linarith
    obtain ⟨S,hSc,hSA,hSZ,M₁,M₂,hp₁,hc₁,hp₂,hc₂,hcross,hold⟩:=
      hN₀ V hn₀ G (A i\B) (Z i) (hZ i).1 (hZ i).2 hdeg hmiss'
    refine ⟨S,hSc,⟨hSA.trans (Finset.sdiff_subset),hSZ,⟨M₁,M₂,hp₁,hc₁,hp₂,hc₂,hcross,hold⟩⟩,?_⟩
    exact Finset.disjoint_left.mpr (by intro x hxS hxB;exact (Finset.mem_sdiff.mp (hSA hxS)).2 hxB)
  obtain ⟨S,hS,hdis⟩:=finite_fresh_sets s P hchoose
  exact ⟨S,fun i=>⟨(hS i).1,(hS i).2.1,(hS i).2.2.1,(hS i).2.2.2⟩,hdis⟩
end Oberwolfach
