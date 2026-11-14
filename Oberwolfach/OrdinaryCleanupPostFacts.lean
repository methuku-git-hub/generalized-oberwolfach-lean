module

public import Oberwolfach.OrdinaryPackingPostFacts

@[expose] public section
/-! The sparse cleanup leaves an actual balanced divisible physical remainder
with no outside-outside edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryCleanupUsedGraph (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) (K:OrdinaryOutsideCleanupData Q F H X Z C r t):SimpleGraph (V⊕U):=
  ordinaryPhysicalGraph (wheelFamilyRim K.wheels) (wheelFamilySpokes K.wheels)

def ordinaryCleanupPostRim (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) (K:OrdinaryOutsideCleanupData Q F H X Z C r t):SimpleGraph V:=
  Q\wheelFamilyRim K.wheels

def ordinaryCleanupPostSpokes (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) (K:OrdinaryOutsideCleanupData Q F H X Z C r t):V→U→Prop:=
  fun v u=>H v u∧¬wheelFamilySpokes K.wheels v u

structure OrdinaryCleanupPostFacts (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) (K:OrdinaryOutsideCleanupData Q F H X Z C r t):Prop where
  exact_remainder:ordinaryPhysicalGraph (ordinaryCleanupPostRim Q F H X Z C r t K)
    (ordinaryCleanupPostSpokes Q F H X Z C r t K)=ordinaryPhysicalGraph Q H\ordinaryCleanupUsedGraph Q F H X Z C r t K
  no_outer_rim:∀v∉X,∀w∉X,¬(ordinaryCleanupPostRim Q F H X Z C r t K).Adj v w
  no_outer_spoke:∀v∉X,∀u∉Z,¬ordinaryCleanupPostSpokes Q F H X Z C r t K v u
  balance:∀v,(ordinaryCleanupPostRim Q F H X Z C r t K).degree v=
    2*(Finset.univ.filter (ordinaryCleanupPostSpokes Q F H X Z C r t K v)).card
  divisible:∀u,r∣(Finset.univ.filter (fun v=>ordinaryCleanupPostSpokes Q F H X Z C r t K v u)).card
  degree:∀w,(ordinaryCleanupUsedGraph Q F H X Z C r t K).degree w≤t
  avoids_prior:Disjoint (ordinaryCleanupUsedGraph Q F H X Z C r t K) C

theorem ordinary_cleanup_post_facts (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) (K:OrdinaryOutsideCleanupData Q F H X Z C r t)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    OrdinaryCleanupPostFacts Q F H X Z C r t K:=by
  have hsub:=wheelFamily_subhost K.wheels
  have hb:=ordinary_decomposition_remainder_balance Q (wheelFamilyRim K.wheels) H (wheelFamilySpokes K.wheels) r
    hsub.1 hsub.2 hbal hdiv K.decomposition
  have he:ordinaryPhysicalGraph (ordinaryCleanupPostRim Q F H X Z C r t K)
      (ordinaryCleanupPostSpokes Q F H X Z C r t K)=ordinaryPhysicalGraph Q H\ordinaryCleanupUsedGraph Q F H X Z C r t K:=by
    ext a b
    cases a with
    | inl v=>cases b with
      | inl w=>rfl
      | inr u=>rfl
    | inr u=>cases b with
      | inl v=>rfl
      | inr u'=>simp [ordinaryPhysicalGraph,ordinaryCleanupPostRim,ordinaryCleanupPostSpokes,ordinaryCleanupUsedGraph]
  refine ⟨he,K.no_outer_rim,K.no_outer_spoke,?_,?_,K.degree,K.avoids_prior⟩
  · convert hb.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hb.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
