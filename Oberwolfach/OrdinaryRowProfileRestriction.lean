module

public import Oberwolfach.OrdinaryRelativeProfileRestriction

@[expose] public section

/-! Restrict the original common-cycle weights only by deleting row labels.
The host graph and every surviving coefficient stay fixed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl : Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_row_profile_restriction (r : ℕ) (hr : 3≤r)
    (S : Tpl → VertexAbsorberTemplate r) (β a b B τ : ℝ)
    (hβ : 0<β) (ha : 0<a) (hb : 0<b) (hB : 0<B) (hτ : 0<τ) :
    ∃ ε : ℝ,0<ε ∧ ε≤β/2 ∧ ∃ N : ℕ,1≤N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (Q F : SimpleGraph V) (T Z : Finset V),
      β*Fintype.card V≤(T.card:ℝ) → (Z.card:ℝ)≤ε*Fintype.card V →
      ∀ w : LocalOrdinaryCycle Q F T r → ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^(r-1)≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1)) →
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤τ/4) →
      (∀ X : Finset V,X⊆T → X.card=r →
        a*(Fintype.card V:ℝ)^(r*r)≤Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) S X)) →
      let k := ((T\Z).card:ℝ)/r
      let w' := fun C : LocalOrdinaryCycle Q F (T\Z) r=>
        w (localOrdinaryRestrictionParent le_rfl Finset.sdiff_subset C)
      0<k ∧ (β/2)*Fintype.card V≤(r:ℝ)*k ∧ (r:ℝ)*k≤Fintype.card V ∧
      (∀ C,(b*(β/2)^(r-1)/(r:ℝ)^(r-1))/k^(r-1)≤w' C ∧
        w' C≤(B/(r:ℝ)^(r-1))/k^(r-1)) ∧
      (∀ v∈T\Z,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤3*τ/4) ∧
      (∀ X : Finset V,X⊆T\Z → X.card=r →
        ((a/2)*(r:ℝ)^(r*r))*k^(r*r)≤
          Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T\Z) (r:=r)) S X)) := by
  obtain ⟨ε,hε,hεβ,hN⟩ := ordinary_relative_profile_restriction r hr S β a b B τ hβ ha hb hB hτ
  obtain ⟨N,hN1,hN⟩ := hN 0
  refine ⟨ε,hε,hεβ,N,hN1,?_⟩
  intro V _ _ hn Q F T Z hT hZ w hw herr habs
  have hh := hN V hn Q ⊥ F T Z hT hZ (by simp) w hw herr habs
  have hQ : Q \ (⊥ : SimpleGraph V)=Q := by ext v u; simp
  let P : ∀ Q' : SimpleGraph V,Q'≤Q→Prop := fun Q' hq =>
      let k := ((T\Z).card:ℝ)/r
      let w' := fun C : LocalOrdinaryCycle Q' F (T\Z) r=>
        w (localOrdinaryRestrictionParent hq Finset.sdiff_subset C)
      0<k ∧ (β/2)*Fintype.card V≤(r:ℝ)*k ∧ (r:ℝ)*k≤Fintype.card V ∧
      (∀ C,(b*(β/2)^(r-1)/(r:ℝ)^(r-1))/k^(r-1)≤w' C ∧
        w' C≤(B/(r:ℝ)^(r-1))/k^(r-1)) ∧
      (∀ v∈T\Z,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤3*τ/4) ∧
      (∀ X : Finset V,X⊆T\Z → X.card=r →
        ((a/2)*(r:ℝ)^(r*r))*k^(r*r)≤
          Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q') (F:=F) (T:=T\Z) (r:=r)) S X))
  change P Q le_rfl
  have hh' : ∃ hq : Q\(⊥:SimpleGraph V)≤Q,P (Q\⊥) hq := ⟨sdiff_le,hh⟩
  rw [hQ] at hh'
  obtain ⟨hq,hp⟩ := hh'
  exact hp

end Oberwolfach
