module

public import Oberwolfach.TriangleTransformerFreshSpokeFactors

@[expose] public section
/-! Near-full common spoke neighbourhoods remain near-full after removing
one bounded forbidden set. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem triangular_transformer_common_hub_available
    {V U:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (K:V→U→Prop) (u u':U) (W:Finset V) (ε:ℝ)
    (hnear:∀ z:U,(((Finset.univ:Finset V).filter (fun v=>¬K v z)).card:ℝ)≤ε*(Fintype.card V:ℝ)):
    let A:=((Finset.univ:Finset V).filter (fun v=>K v u∧K v u'))\W
    (∀ v∈A,K v u∧K v u') ∧ Disjoint A W ∧
      (((Finset.univ:Finset V)\A).card:ℝ)≤2*ε*(Fintype.card V:ℝ)+(W.card:ℝ) := by
  intro A
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp hv).2 hw
  · let B:Finset V:=(Finset.univ.filter (fun v=>¬K v u))∪(Finset.univ.filter (fun v=>¬K v u'))∪W
    have hsub:(Finset.univ:Finset V)\A⊆B:=by
      intro v hv
      simp only [A,B,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_filter,Finset.mem_union] at hv ⊢
      tauto
    have hc:B.card≤((Finset.univ:Finset V).filter (fun v=>¬K v u)).card+
        ((Finset.univ:Finset V).filter (fun v=>¬K v u')).card+W.card:=by
      have h1:=Finset.card_union_le ((Finset.univ:Finset V).filter (fun v=>¬K v u))
        ((Finset.univ:Finset V).filter (fun v=>¬K v u'))
      have h2:=Finset.card_union_le (((Finset.univ:Finset V).filter (fun v=>¬K v u))∪
        ((Finset.univ:Finset V).filter (fun v=>¬K v u'))) W
      dsimp [B]
      omega
    have hcc:(((Finset.univ:Finset V)\A).card:ℝ)≤
        (((Finset.univ:Finset V).filter (fun v=>¬K v u)).card:ℝ)+
        (((Finset.univ:Finset V).filter (fun v=>¬K v u')).card:ℝ)+(W.card:ℝ):=by
      exact_mod_cast (Finset.card_le_card hsub).trans hc
    have h1:=hnear u
    have h2:=hnear u'
    linarith
end Oberwolfach
