module

public import Oberwolfach.SparseTypedEdgeSetCorrection
public import Oberwolfach.BipartiteNormalizedCutDeletion
public import Oberwolfach.OccurrenceRelationMultiplicity

@[expose] public section

/-! Construct the sparse inner correction while preserving the protected
induced pair. All four allowed cut bounds are derived from the original
host cuts and the sizes of the protected sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_protected_inner_correction (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hh : 0<h) (hδ : 0<δ) (hδsmall : δ<1/4) (hξ : 0<ξ)
    (hξh : ((q:ℝ)+1)*ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
    ∀ (V U E K : Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (tail head : E → V) (ktail khead : K → V),
      Function.Injective (fun e=>(tail e,head e)) → Function.Injective (fun e=>(ktail e,khead e)) →
    ∀ (H₀ Hₖ : V → U → Prop),(∀ v u,¬(H₀ v u∧Hₖ v u))→
    ∀ (π:Equiv.Perm V) (T:Finset V) (W:Finset U),(∀ v,π v∈T↔v∈T)→
      (T.card:ℝ)≤h*Fintype.card V→(W.card:ℝ)≤h*Fintype.card U→
      (∀ v,|occurrenceDegree (Sum.elim tail ktail) v-
        (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      (∀ v,|occurrenceDegree (Sum.elim head khead) v-
        (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      (∀ v,|occurrenceDegree khead v-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      (∀ u,|(∑ v,if H₀ v u then (1:ℝ) else 0)-(q:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      BipartiteLargeCut (occurrenceMultiplicity tail head) δ (2*h)→
      BipartiteLargeCut (occurrenceMultiplicity ktail khead) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity H₀) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity Hₖ) δ (2*h)→
    let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨Hₖ z.1 z.2)
    ∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)), DS⊆S ∧
      (∀ v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ u,((DS.filter (fun z=>z.2=u)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (DA.card:ℝ)≤8*((q:ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      (DS.card:ℝ)≤4*((q:ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      MarkedRemainderDivisible tail head ktail khead Hₖ (Finset.univ\DA) (S\DS) q ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ :=by
  obtain ⟨η₀,hη₀,N,hN⟩:=sparse_typed_edge_set_correction q hq ω h δ ξ hω hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,max N 1,?_⟩
  intro η hη hηsmall V U E K _ _ _ _ _ _ hn hωn hun tail head ktail khead hinj hkinj
    H₀ Hₖ hH π T W hT hTsize hWsize hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK S
  have hnpos:0<Fintype.card V:=by have hh':=(le_max_right N 1).trans hn;omega
  have hupos:0<Fintype.card U:=by
    have hv:(0:ℝ)<Fintype.card V:=by exact_mod_cast hnpos
    have hu:(0:ℝ)<Fintype.card U:=(mul_pos hω hv).trans_le hωn
    exact_mod_cast hu
  let R₀:=fun x y=>∃ e:E,tail e=x∧head e=y
  let Rₖ:=fun x y=>∃ e:K,ktail e=x∧khead e=y
  have he₀:occurrenceMultiplicity tail head=relationMultiplicity R₀:=occurrenceMultiplicity_eq_relation tail head hinj
  have heₖ:occurrenceMultiplicity ktail khead=relationMultiplicity Rₖ:=occurrenceMultiplicity_eq_relation ktail khead hkinj
  let A₀:=relationMultiplicity (fun x y=>R₀ x y∧¬(x∈T∧y∈T))
  let Aₖ:=relationMultiplicity (fun x y=>Rₖ x y∧¬(x∈T∧y∈T))
  let T₀:=relationMultiplicity (fun x u=>H₀ x u∧¬(x∈T∧u∈W))
  let Tₖ:=relationMultiplicity (fun x u=>Hₖ x u∧¬(x∈T∧u∈W))
  have hA0:∀ x y,A₀ x y≤occurrenceMultiplicity tail head x y:=by
    intro x y;rw [he₀];exact relationMultiplicity_delete_rectangle_le R₀ T T x y
  have hAK:∀ x y,Aₖ x y≤occurrenceMultiplicity ktail khead x y:=by
    intro x y;rw [heₖ];exact relationMultiplicity_delete_rectangle_le Rₖ T T x y
  have hT0:∀ x u,T₀ x u≤relationMultiplicity H₀ x u:=relationMultiplicity_delete_rectangle_le H₀ T W
  have hTK:∀ x u,Tₖ x u≤relationMultiplicity Hₖ x u:=relationMultiplicity_delete_rectangle_le Hₖ T W
  have hc0:BipartiteLargeCut A₀ δ h:=by
    have ht:=bipartiteLargeCut_delete_rectangle hnpos hnpos R₀ T T δ (2*h) h hh.le hTsize hTsize
      (by rw [←he₀];exact hcut0)
    simpa only [show 2*h-h=h by ring] using ht
  have hcK:BipartiteLargeCut Aₖ δ h:=by
    have ht:=bipartiteLargeCut_delete_rectangle hnpos hnpos Rₖ T T δ (2*h) h hh.le hTsize hTsize
      (by rw [←heₖ];exact hcutK)
    simpa only [show 2*h-h=h by ring] using ht
  have hcs0:BipartiteLargeCut T₀ δ h:=by
    have ht:=bipartiteLargeCut_delete_rectangle hnpos hupos H₀ T W δ (2*h) h hh.le hTsize hWsize hcutH0
    simpa only [show 2*h-h=h by ring] using ht
  have hcsK:BipartiteLargeCut Tₖ δ h:=by
    have ht:=bipartiteLargeCut_delete_rectangle hnpos hupos Hₖ T W δ (2*h) h hh.le hTsize hWsize hcutHK
    simpa only [show 2*h-h=h by ring] using ht
  obtain ⟨DA,DS,hsub,hdeg,hrow,hcol,hcardA,hcardS,hdiv,havoid⟩:=hN η hη hηsmall V U E K
    ((le_max_left _ _).trans hn) hωn hun tail head ktail khead hinj hkinj H₀ Hₖ hH A₀ Aₖ T₀ Tₖ
    hA0 hAK hT0 hTK hbp hbm hbk hbw hc0 hcK hcs0 hcsK
  refine ⟨DA,DS,hsub,hdeg,hrow,hcol,hcardA,hcardS,hdiv,?_⟩
  apply havoid π T W hT
  · intro x hx y hy;simp only [A₀,relationMultiplicity,hx,hy,and_self,not_true_eq_false,and_false,ite_false]
  · intro x hx y hy;simp only [Aₖ,relationMultiplicity,hx,hy,and_self,not_true_eq_false,and_false,ite_false]
  · intro x hx u hu;simp only [T₀,relationMultiplicity,hx,hu,and_self,not_true_eq_false,and_false,ite_false]
  · intro x hx u hu;simp only [Tₖ,relationMultiplicity,hx,hu,and_self,not_true_eq_false,and_false,ite_false]

end Oberwolfach
