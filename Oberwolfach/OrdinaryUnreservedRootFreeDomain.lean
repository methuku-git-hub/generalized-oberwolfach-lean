module

public import Oberwolfach.OrdinaryUnreservedAfterRootCover

@[expose] public section
/-! The complete unreserved physical target is already supported on the
complements of the covered deep roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_root_free_domain
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (A:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (R:SimpleGraph (V⊕U)):
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    let G:=ordinaryPhysicalGraph (ordinaryUnreservedRim Q' X R) (ordinaryUnreservedSpokes H' X Z R);
    G=spanningRestriction G (ordinaryInnerVertices (Finset.univ\T) (Finset.univ\W)):=by
  intro Q' H' G
  have hnone:=ordinary_unreserved_after_root_cover Q F H X T Z W r η ell hTX hWZ A R
  have hleft (a b:V⊕U) (hab:G.Adj a b):a∈ordinaryInnerVertices (Finset.univ\T) (Finset.univ\W):=by
    cases a with
    | inl v=>
      apply (ordinaryInnerVertices_left _ _ v).mpr
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
      intro hv
      cases b with
      | inl w=>exact hnone.1 v hv w hab
      | inr u=>exact hnone.2.1 v hv u hab
    | inr u=>
      apply (ordinaryInnerVertices_right _ _ u).mpr
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
      intro hu
      cases b with
      | inl v=>exact hnone.2.2 u hu v hab
      | inr z=>exact hab.elim
  apply le_antisymm
  · intro a b hab
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨hab,hleft a b hab,hleft b a hab.symm⟩
  · intro a b hab
    exact ((spanningRestriction_adj _ _ _ _).mp hab).1
end Oberwolfach
