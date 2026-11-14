module

public import Oberwolfach.OrdinaryLocalDeletionCandidates
public import Oberwolfach.ResourceBoundedDeletionLoss

@[expose] public section

/-! The actual local-cycle weights after row and rim deletions are the
original coefficients. The error is measured at the original ambient order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinary_restricted_profile_loads (Q D F : SimpleGraph V) (T Z : Finset V)
    (hr : 2≤r) (hn : 0<Fintype.card V)
    (w : LocalOrdinaryCycle Q F T r → ℝ) (B η : ℝ) (hB : 0≤B)
    (hw : ∀ C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (herr : ∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤η)
    (v : V) (hv : v∈T\Z) :
    |1-hypergraphWeightedDegree localOrdinaryVertices
      (fun C : LocalOrdinaryCycle (Q\D) F (T\Z) r=>
        w (localOrdinaryRestrictionParent sdiff_le Finset.sdiff_subset C)) v|≤
      η+(Z.card+D.edgeFinset.card:ℕ)*((r^r:ℕ)*B/Fintype.card V) := by
  have hpair := ambient_resource_pair_weight localOrdinaryVertices r (r^r) hr
    localOrdinaryVertices_card (local_ordinary_multiplicity Q F T)
    w B hB hn (fun C=>(hw C).2)
  have hh := candidate_degree_restriction_loss localOrdinaryVertices w (fun C=>(hw C).1)
    (localOrdinaryRestrictionGood (Q\D) (T\Z)) Z (canonicalGraphPairs D)
    (fun e he=>(canonicalGraphPairs_adj D e he).ne) ((r^r:ℕ)*B/Fintype.card V) hpair
    (fun C hZ hD=>localOrdinaryRestriction_of_avoidance Q D F T Z C hZ hD) v
    (Finset.mem_sdiff.mp hv).2
  rw [←localOrdinaryRestriction_degree Q (Q\D) F T (T\Z) sdiff_le Finset.sdiff_subset w v] at hh
  rw [canonicalGraphPairs_card] at hh
  have he := abs_le.mp (herr v (Finset.mem_sdiff.mp hv).1)
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hcost : (0:ℝ)≤(Z.card+D.edgeFinset.card:ℕ)*((r^r:ℕ)*B/Fintype.card V) := by positivity
  apply abs_le.mpr
  constructor <;> linarith only [hh.1,hh.2,he.1,he.2,hcost]

end Oberwolfach
