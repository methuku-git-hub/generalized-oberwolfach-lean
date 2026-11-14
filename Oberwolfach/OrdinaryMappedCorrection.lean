module

public import Oberwolfach.OrdinaryGraphMapDifference
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! A corrected balanced inner graph pair can be embedded into the ambient
    vertex and hub types with exact subtraction and physical degree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_mapped_spokes_difference (H J:V→U→Prop) (φ:V↪V') (ψ:U↪U'):
    ordinaryMappedSpokes (fun v u=>H v u∧¬J v u) φ ψ =
      (fun v u=>ordinaryMappedSpokes H φ ψ v u∧¬ordinaryMappedSpokes J φ ψ v u):=by
  funext a b
  apply propext
  constructor
  · rintro ⟨v,u,⟨hh,hj⟩,rfl,rfl⟩
    exact ⟨⟨v,u,hh,rfl,rfl⟩,fun h=>hj ((ordinaryMappedSpokes_apply J φ ψ v u).mp h)⟩
  · rintro ⟨⟨v,u,hh,rfl,rfl⟩,hj⟩
    exact ⟨v,u,⟨hh,fun h=>hj ⟨v,u,h,rfl,rfl⟩⟩,rfl,rfl⟩

theorem ordinary_mapped_correction
    (G D:SimpleGraph V) (H J:V→U→Prop) (φ:V↪V') (ψ:U↪U') (r:ℕ) (L:ℝ)
    (hDG:D≤G) (hJH:∀v u,J v u→H v u)
    (hbal:∀v,(G\D).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬J v u)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u∧¬J v u)).card)
    (hL:0≤L) (hrow:∀v,(D.degree v:ℝ)+(Finset.univ.filter (J v)).card≤L)
    (hcol:∀u,((Finset.univ.filter (fun v=>J v u)).card:ℝ)≤L):
    let C:=G.map φ;let K:=ordinaryMappedSpokes H φ ψ;
    let D':=D.map φ;let J':=ordinaryMappedSpokes J φ ψ;
    D'≤C ∧ (∀v u,J' v u→K v u) ∧
    (∀v,(C\D').degree v=2*(Finset.univ.filter (fun u=>K v u∧¬J' v u)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>K v u∧¬J' v u)).card) ∧
    (∀x:V'⊕U',((ordinaryPhysicalGraph D' J').degree x:ℝ)≤L):=by
  intro C K D' J'
  have hD:D'≤C:=by
    intro a b hab
    obtain ⟨v,w,hvw,rfl,rfl⟩:=(SimpleGraph.map_adj φ D a b).mp hab
    exact SimpleGraph.map_adj_apply.mpr (hDG hvw)
  have hJ:∀v u,J' v u→K v u:=by
    intro a b h
    obtain ⟨v,u,hvu,rfl,rfl⟩:=h
    exact ⟨v,u,hJH v u hvu,rfl,rfl⟩
  have hbalance:=ordinary_pair_embedding_balance (G\D) (fun v u=>H v u∧¬J v u) φ ψ
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hdivis:=ordinary_pair_embedding_divisibility (fun v u=>H v u∧¬J v u) φ ψ r
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  simp only [ordinary_mapped_spokes_difference] at hbalance
  simp only [ordinary_mapped_spokes_difference] at hdivis
  refine ⟨hD,hJ,?_,?_,?_⟩
  · intro v
    have hg:=congrArg (fun A:SimpleGraph V'=>A.neighborFinset v) (simpleGraph_map_difference φ G D)
    have hd:=congrArg Finset.card hg
    have he:((G\D).map φ).degree v=(C\D').degree v:=by
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hd
      convert hd using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hb:=hbalance v
    have hh:((G\D).map φ).degree v=2*(Finset.univ.filter (fun u=>K v u∧¬J' v u)).card:=by
      convert hb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact he.symm.trans hh
  · intro u;convert hdivis u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  intro x
  change ((ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes J φ ψ)).degree x:ℝ)≤L
  cases x with
  | inl a=>
    by_cases ha:a∈Set.range φ
    · obtain ⟨v,rfl⟩:=ha
      rw [ordinary_physical_degree_row,SimpleGraph.degree_map_apply,ordinaryMappedSpokes_row,
        Finset.card_image_of_injective _ ψ.injective,Nat.cast_add]
      exact hrow v
    · have hz:(D.map φ).degree a=0:=by
        convert simpleGraph_map_degree_outside D φ a ha using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
      have hs:Finset.univ.filter (ordinaryMappedSpokes J φ ψ a)=∅:=ordinaryMappedSpokes_row_outside J φ ψ a ha
      have hz':((D.map φ).degree a:ℝ)=0:=by exact_mod_cast hz
      have hs':((Finset.univ.filter (ordinaryMappedSpokes J φ ψ a)).card:ℝ)=0:=by rw [hs];simp
      have hp:((ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes J φ ψ)).degree (Sum.inl a):ℝ)=
          ((D.map φ).degree a:ℝ)+(Finset.univ.filter (ordinaryMappedSpokes J φ ψ a)).card:=by
        have ht:=ordinary_physical_degree_row (D.map φ) (ordinaryMappedSpokes J φ ψ) a
        have ht':(ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes J φ ψ)).degree (Sum.inl a)=
            (D.map φ).degree a+(Finset.univ.filter (ordinaryMappedSpokes J φ ψ a)).card:=by
          convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
        exact_mod_cast ht'
      rw [hp,hz',hs',add_zero]
      exact hL
  | inr b=>
    by_cases hb:b∈Set.range ψ
    · obtain ⟨u,rfl⟩:=hb
      rw [ordinary_physical_degree_column,ordinaryMappedSpokes_column,Finset.card_image_of_injective _ φ.injective]
      exact hcol u
    · rw [ordinary_physical_degree_column,ordinaryMappedSpokes_column_outside J φ ψ b hb]
      simpa using hL
end Oberwolfach
