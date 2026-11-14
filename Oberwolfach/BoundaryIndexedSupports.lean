module

public import Oberwolfach.BoundarySelectionSupports
public import Oberwolfach.EmbeddedFiniteSets

@[expose] public section

/-! Boundary supports on the inner vertex subtype, indexed by the actual
outside roots. Memberships count each outside root once, even when the
number of roots is larger than the inner domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V J:Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

def innerBoundarySupport (G:SimpleGraph V) (A:Finset V) (x:V):Finset A:=
  Finset.univ.filter (fun v=>G.Adj x v.val)

theorem innerBoundarySupport_image (G:SimpleGraph V) (A:Finset V) (x:V):
    (innerBoundarySupport G A x).image Subtype.val=A∩G.neighborFinset x:=by
  ext v
  simp only [innerBoundarySupport,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_inter,SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩;exact ⟨w.property,hw⟩
  · rintro ⟨hv,hw⟩;exact ⟨⟨v,hv⟩,hw,rfl⟩

theorem innerBoundarySupport_card (G:SimpleGraph V) (A:Finset V) (x:V):
    (innerBoundarySupport G A x).card=(A∩G.neighborFinset x).card:=by
  rw [←innerBoundarySupport_image]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

theorem innerBoundarySupport_inter_card (G:SimpleGraph V) (A:Finset V) (x y:V):
    (innerBoundarySupport G A x∩innerBoundarySupport G A y).card=
      ((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card:=by
  rw [←innerBoundarySupport_image G A x,←innerBoundarySupport_image G A y,
    ←Finset.image_inter _ _ Subtype.val_injective]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

theorem innerBoundarySupport_membership_bound (G:SimpleGraph V) (A Z:Finset V)
    (x:J↪V) (hx:∀ j,x j∈Z) (v:A):
    (Finset.univ.filter (fun j=>v∈innerBoundarySupport G A (x j))).card≤
      (Z.filter (fun z=>v.val∈A∩G.neighborFinset z)).card:=by
  have hs:((Finset.univ.filter (fun j=>v∈innerBoundarySupport G A (x j))).image x)⊆
      Z.filter (fun z=>v.val∈A∩G.neighborFinset z):=by
    intro z hz
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hz
    have hh:G.Adj (x j) v.val:=by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,innerBoundarySupport] using hj
    exact Finset.mem_filter.mpr ⟨hx j,Finset.mem_inter.mpr ⟨v.property,(SimpleGraph.mem_neighborFinset _ _ _).mpr hh⟩⟩
  have hh:=Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ x.injective] using hh

theorem boundary_indexed_selection_supports (P G:SimpleGraph V) (A Z:Finset V)
    (x:J↪V) (hx:∀ j,x j∈Z) (τ κ ε:ℝ) (hτ:0≤τ) (hτ1:τ≤1) (hκ:0<κ) (hκ1:κ≤1)
    (hsize:κ*Fintype.card V≤(A.card:ℝ)) (herr:ε≤τ^2*A.card)
    (hrow:∀ x,|((A∩G.neighborFinset x).card:ℝ)-τ*(A∩P.neighborFinset x).card|≤ε)
    (hpair:∀ x y,x≠y→
      |(((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card:ℝ)-
        τ^2*((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card|≤ε)
    (hcol:∀ v∈A,|((Z.filter (fun x=>v∈A∩G.neighborFinset x)).card:ℝ)-
      τ*(Z∩P.neighborFinset v).card|≤ε):
    (∀ i,((innerBoundarySupport G A (x i)).card:ℝ)≤2*τ*Fintype.card A) ∧
    (∀ i j,i≠j→((innerBoundarySupport G A (x i)∩innerBoundarySupport G A (x j)).card:ℝ)≤
      (3*τ/κ)^2*Fintype.card A) ∧
    (∀ v:A,((Finset.univ.filter (fun i=>v∈innerBoundarySupport G A (x i))).card:ℝ)≤
      (3*τ/κ)*Fintype.card A):=by
  obtain ⟨hr,hp,hc⟩:=boundary_selection_supports P G A Z τ κ ε hτ hτ1 hκ hκ1 hsize herr hrow hpair hcol
  simp only [Fintype.card_coe]
  refine ⟨?_,?_,?_⟩
  · intro i;rw [innerBoundarySupport_card];exact hr _
  · intro i j hij;rw [innerBoundarySupport_inter_card];exact hp _ _ (fun h=>hij (x.injective h))
  · intro v
    exact (Nat.cast_le.mpr (innerBoundarySupport_membership_bound G A Z x hx v)).trans (hc v.val)

theorem outer_roots_fit_quadratic_local_order (n a j:ℕ) (κ:ℝ) (hκ:0<κ)
    (ha:κ*n≤(a:ℝ)) (hsmall:1/κ≤(a:ℝ)) (hj:j≤n):j≤a^2:=by
  have hn:(n:ℝ)≤(a:ℝ)/κ:=by
    apply (le_div_iff₀ hκ).mpr;simpa only [mul_comm] using ha
  have hh:(a:ℝ)/κ≤(a:ℝ)^2:=by
    have hm:=mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg a)
    convert hm using 1 <;> ring
  have he:(j:ℝ)≤(a:ℝ)^2:=(Nat.cast_le.mpr hj).trans (hn.trans hh)
  exact_mod_cast he

end Oberwolfach
