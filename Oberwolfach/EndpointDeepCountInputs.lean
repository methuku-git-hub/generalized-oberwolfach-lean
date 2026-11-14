module

public import Oberwolfach.EndpointSourceCounts
public import Oberwolfach.OrdinaryPhysicalGraphDifference

@[expose] public section
/-! The two-domain and physical forms of the deeper row and hub estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure EndpointTypedDeepCounts (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (pR pH ε:ℝ):Prop where
  rows:∀S:Finset V,∀J:Finset U,J⊆B→S.card≤3→J.card≤2→S.card+J.card≤4→
    pR^S.card*pH^J.card*(common A S (fun v=>(P\F).neighborFinset v)).card-ε*A.card≤
      ((common (common A S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)
  indices:∀S:Finset V,S.card≤3→(∀v∈S,∀w∈S,¬F.Adj v w)→
    (pH^S.card-ε)*B.card≤((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)

structure EndpointPhysicalDeepCounts (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (pR pH ε:ℝ):Prop where
  rows:∀S J:Finset (V⊕U),S⊆Finset.univ.image Sum.inl→J⊆B.image Sum.inr→
    S.card≤3→J.card≤2→S.card+J.card≤4→
    pR^S.card*pH^J.card*
      (common (A.image Sum.inl) S (fun v=>((ordinaryPhysicalGraph P (fun _ _=>False))\
        (ordinaryPhysicalGraph F (fun _ _=>False))).neighborFinset v)).card-ε*A.card≤
    ((common (common (A.image Sum.inl) S (fun v=>(ordinaryPhysicalGraph Q (fun _ _=>False)).neighborFinset v)) J
      (fun u=>(ordinaryPhysicalGraph ⊥ H).neighborFinset u)).card:ℝ)
  indices:∀S:Finset (V⊕U),S⊆Finset.univ.image Sum.inl→S.card≤3→
    (∀v∈S,∀w∈S,¬(ordinaryPhysicalGraph F (fun _ _=>False)).Adj v w)→
    (pH^S.card-ε)*B.card≤((common (B.image Sum.inr) S (fun v=>(ordinaryPhysicalGraph ⊥ H).neighborFinset v)).card:ℝ)
end Oberwolfach
