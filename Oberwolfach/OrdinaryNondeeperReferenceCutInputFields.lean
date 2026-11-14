module

public import Oberwolfach.OrdinaryVortexNondeeperTriangleInputs

@[expose] public section
/-! Feed the fixed nondeeper host and permutation inputs to the joint rim
and spoke reference-cut theorem without choosing another local sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nondeeper_reference_cut_input_fields
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize d:ℕ) (β ε ρ₀ θ α εTri pR pH:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (πA:∀i,Equiv.Perm (ordinaryVortexNondeeperVertexType Q i)) (L:ℕ)
    (hθ:1/2≤θ)
    (hinputs:∀i≤L,OrdinaryNondeeperTriangleLocalInputs P D vsize d β ε ρ₀ θ α εTri pR pH Q π i (πA i)):
    let W:=ordinaryVortexNondeeperVertexType Q
    let Z:=ordinaryVortexNondeeperHubType Q
    let f:=ordinaryVortexNondeeperVertexEmbedding Q
    let F:=permutationConflictGraph π (3*d);
    (∀i≤L,(ρ₀/4)*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i)) ∧
    (∀i≤L,∀v,(1/2+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ)) ∧
    (∀i≤L,∀v,((F.comap (f i)).degree v:ℝ)≤2*(3*d)) ∧
    (∀i≤L,∀x l,0<l→l<2*d+1→((πA i)^l) x≠x) :=by
  intro W Z f F
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    exact ⟨(hinputs i hi).hub_lower,(hinputs i hi).hub_upper⟩
  · intro i hi v
    have hm:=(hinputs i hi).min_degree v
    have hc:=mul_le_mul_of_nonneg_right (show (1/2+α:ℝ)≤θ+α by linarith)
      (show (0:ℝ)≤Fintype.card (W i) by positivity)
    exact hc.trans hm
  · intro i hi v
    have he:=congrArg (fun G:SimpleGraph (W i)=>G.neighborFinset v) (hinputs i hi).conflict_restriction
    have hc:=congrArg Finset.card he
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    have hd:((F.comap (f i)).degree v)≤2*(3*d):=by
      convert hc.le.trans ((hinputs i hi).conflict_degree v) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact_mod_cast hd
  · intro i hi
    exact (hinputs i hi).no_short
end Oberwolfach
