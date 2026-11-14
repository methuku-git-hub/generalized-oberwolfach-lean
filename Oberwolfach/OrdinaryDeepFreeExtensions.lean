module

public import Oberwolfach.OrdinaryDeepSafeHost

@[expose] public section
/-! Restricting the internal path reservoir away from the deeper rim loses
at most the size of that rim from any common-extension count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_free_extension_count (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (u:U) (a c:V):
    (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ) ≤
      ((((X\T).filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)+T.card := by
  let S:Finset V := (X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c
  let S':Finset V := ((X\T).filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c
  have hsub:S\T⊆S' := by
    intro v hv
    have hvS:v∈S:=(Finset.mem_sdiff.mp hv).1
    have hvT:v∉T:=(Finset.mem_sdiff.mp hv).2
    simp only [S,Finset.mem_inter,Finset.mem_filter] at hvS
    simp only [S',Finset.mem_inter,Finset.mem_filter,Finset.mem_sdiff]
    exact ⟨⟨⟨⟨hvS.1.1.1,hvT⟩,hvS.1.1.2⟩,hvS.1.2⟩,hvS.2⟩
  have hc:=Finset.card_sdiff_add_card_inter S T
  have hi:(S∩T).card≤T.card:=Finset.card_le_card Finset.inter_subset_right
  have hs:(S\T).card≤S'.card:=Finset.card_le_card hsub
  have hn:S.card≤S'.card+T.card:=by omega
  exact_mod_cast hn
end Oberwolfach
