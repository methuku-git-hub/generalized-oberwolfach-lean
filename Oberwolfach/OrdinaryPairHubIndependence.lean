module

public import Oberwolfach.OrdinaryPairHubMarginals

@[expose] public section

/-! Distinct resources of a candidate wheel read disjoint raw coordinates
when its vertices avoid the permutation-conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPairHubForget : Sym2 V⊕(V×U)→Sym2 V⊕(V×Unit)
  | Sum.inl e=>Sum.inl e
  | Sum.inr a=>Sum.inr (a.1,())

theorem ordinary_pair_hub_embedding_forget (u:U) (a:Sym2 V⊕(V×Unit)):
    ordinaryPairHubForget (ordinaryPairHubEmbedding u a)=a := by
  cases a with
  | inl e=>rfl
  | inr a=>rcases a with ⟨v,⟨⟩⟩;rfl

theorem ordinary_pair_hub_candidate_coordinates_disjoint
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ)
    (hF:permutationConflictGraph π (3*d)≤F)
    (W:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r)
    (u u':U) (a b:Sym2 V⊕(V×Unit))
    (ha:a∈ordinaryWheelResources W) (hb:b∈ordinaryWheelResources W) (hne:a≠b):
    Disjoint (ordinaryPairHubCoordinates π d u u' a) (ordinaryPairHubCoordinates π d u u' b) := by
  have hone (i j:U):Disjoint
      (rawWheelResourceCoordinates π d (ordinaryPairHubEmbedding i a))
      (rawWheelResourceCoordinates π d (ordinaryPairHubEmbedding j b)):=by
    apply rawWheelResourceCoordinates_disjoint π d _ _
    · intro hh
      have hh':=congrArg ordinaryPairHubForget hh
      rw [ordinary_pair_hub_embedding_forget,ordinary_pair_hub_embedding_forget] at hh'
      exact hne hh'
    · intro v i' w j' hi hj
      have hi':a=Sum.inr (v,()):=by
        have hh:=congrArg ordinaryPairHubForget hi
        change ordinaryPairHubForget (ordinaryPairHubEmbedding i a)=Sum.inr (v,()) at hh
        rw [ordinary_pair_hub_embedding_forget] at hh
        exact hh
      have hj':b=Sum.inr (w,()):=by
        have hh:=congrArg ordinaryPairHubForget hj
        change ordinaryPairHubForget (ordinaryPairHubEmbedding j b)=Sum.inr (w,()) at hh
        rw [ordinary_pair_hub_embedding_forget] at hh
        exact hh
      by_cases hij:i'≠j'
      · exact Or.inl hij
      · right
        intro hc
        have hvw:v≠w:=by
          intro hh
          exact hne (by rw [hi',hj',hh])
        have hv:v∈(ordinaryWheelRim W).support:=by
          rw [hi',ordinaryWheelResources_spoke] at ha
          exact ha.2
        have hw:w∈(ordinaryWheelRim W).support:=by
          rw [hj',ordinaryWheelResources_spoke] at hb
          exact hb.2
        exact W.property.2 v hv w hw (hF ⟨hvw,hc⟩)
  unfold ordinaryPairHubCoordinates
  exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hone u u,hone u u'⟩,
    Finset.disjoint_union_right.mpr ⟨hone u' u,hone u' u'⟩⟩
end Oberwolfach
