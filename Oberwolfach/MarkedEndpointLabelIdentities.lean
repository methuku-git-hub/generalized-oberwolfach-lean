module

public import Oberwolfach.MarkedEndpointColumnEstimates
public import Oberwolfach.MarkedRestrictedDegreeCentres

@[expose] public section

/-! Endpoint labels are precisely the actual restricted sampled arcs of
one fixed type and direction, including the incoming marked centre pi(x). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_single_arc_domain
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ) (A : Finset V)
    (mark incoming : Bool) (x : V) :
    markedRowDomain P π b A {(mark,incoming,x)} ∅=
      markedDegreeDomain P π b mark incoming x A := by
  ext z
  cases mark <;> cases incoming <;>
    simp [markedRowDomain,markedRowEligible,markedRowRim,markedDegreeDomain,markedDegreeEndpoints,
      P.adj_comm]

theorem marked_endpoint_labels_actual
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (mark incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color) :
    markedEndpointLabels P π d A (mark,incoming,x) σ=
      A.filter (fun z=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark
        (if incoming then z else x) (if incoming then x else z)=1) := by
  ext z
  rw [markedEndpointLabels,marked_single_arc_domain]
  cases mark <;> cases incoming <;>
    simp [Finset.mem_filter,markedDegreeDomain,markedDegreeEndpoints,rawMarkedPairRims,
      markedRowRim,markedPhysicalRim_eq_one_iff,permutationClose_symm π (3*d)] <;> tauto

theorem marked_endpoint_labels_card
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (mark incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color) :
    (markedEndpointLabels P π d A (mark,incoming,x) σ).card=
      markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming x A := by
  rw [marked_endpoint_labels_actual,Finset.card_filter]
  unfold markedRestrictedDegree
  apply Finset.sum_congr rfl
  intro z hz
  simp only [markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation]
  split_ifs <;> simp_all

theorem marked_endpoint_labels_parent_error
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (hInv : ∀ z,π z∈A ↔ z∈A) (mark incoming : Bool) (x : V)
    (σ : RawMarkedOutcome V U Γ Color) (p err D delta : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (hcount : |((markedEndpointLabels P π d A (mark,incoming,x) σ).card:ℝ)-
      p*(markedRowDomain P π (3*d) A {(mark,incoming,x)} ∅).card|≤err)
    (hparent : |((P.neighborFinset (if mark && incoming then π x else x)∩A).card:ℝ)-D|≤delta) :
    |((markedEndpointLabels P π d A (mark,incoming,x) σ).card:ℝ)-p*D|≤
      err+(6*(d:ℝ)+1)+p*delta := by
  rw [marked_endpoint_labels_card,marked_single_arc_domain] at hcount
  have he := markedRestrictedDegree_parent_error P π (3*d) (fun e=>σ (Sum.inl e))
    mark incoming x A hInv p err hp hp1 hcount
  rw [marked_endpoint_labels_card]
  have hdiff : |p*((P.neighborFinset (if mark && incoming then π x else x)∩A).card:ℝ)-p*D|≤p*delta := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left hparent hp
  have hc := (abs_sub_le (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming x A:ℝ)
    (p*((P.neighborFinset (if mark && incoming then π x else x)∩A).card:ℝ)) (p*D)).trans (add_le_add he hdiff)
  convert hc using 1 <;> push_cast <;> ring

end Oberwolfach
