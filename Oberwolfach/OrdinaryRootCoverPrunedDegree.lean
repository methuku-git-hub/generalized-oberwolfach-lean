module

public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.OrdinaryDeepRootFreeFamilies

@[expose] public section
/-! Removing the protected-root star from the cover leaves a globally
bounded-degree graph, even though the full cover may be large at the roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_pruned_degree
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell) (hell:0≤ell):
    ∀w:V⊕U,(((ordinaryPhysicalGraph D.rim D.spokes)\ordinaryDeepRootStar T W).degree w:ℝ)≤ell:=by
  intro w
  let E:=ordinaryPhysicalGraph D.rim D.spokes
  let E':=E\ordinaryDeepRootStar T W
  by_cases hw:w∈ordinaryInnerVertices T W
  · have hzero:∀x,¬E'.Adj w x:=by
      intro x hx
      have hn:¬(ordinaryDeepRootStar T W).Adj w x:=hx.2
      cases w with
      | inl v =>
        have hv:v∈T:=by simpa [ordinaryInnerVertices_left] using hw
        cases x with
        | inl z =>
          have hne:v≠z:=D.rim.ne_of_adj hx.1
          apply hn
          simp [ordinaryDeepRootStar,ordinaryPhysicalGraph,ordinaryRimRootStar,hv,hne]
        | inr u =>
          apply hn
          simp [ordinaryDeepRootStar,ordinaryPhysicalGraph,ordinarySpokeRootStar,hv]
      | inr u =>
        have hu:u∈W:=by simpa [ordinaryInnerVertices_right] using hw
        cases x with
        | inl v =>
          apply hn
          simp [ordinaryDeepRootStar,ordinaryPhysicalGraph,ordinarySpokeRootStar,hu]
        | inr z =>
          exact hx.1
    have hnb:E'.neighborFinset w=∅:=by
      ext x
      constructor
      · intro hx
        exact False.elim (hzero x ((E'.mem_neighborFinset w x).mp hx))
      · intro hx
        exact False.elim (by simpa using hx)
    have hdeg:E'.degree w=0:=by rw [←SimpleGraph.card_neighborFinset_eq_degree,hnb];rfl
    have hh:(E'.degree w:ℝ)≤ell:=by rw [hdeg];simpa using hell
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · have hd:((E'.degree w):ℝ)≤(E.degree w:ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le (show E'≤E from sdiff_le) (v:=w)
    have hh:=D.nonroot_degree w hw
    convert hd.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
