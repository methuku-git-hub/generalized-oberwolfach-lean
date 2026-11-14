module

public import Oberwolfach.MarkedExtensionDomains

@[expose] public section

/-! The one- and two-root domains used in the marked absorber. All roots
are ambient vertices. In particular no separation of the fixed roots is
assumed; only the new vertex is excluded from their permutation intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

def markedSameDirectionSetRequests (j a:Bool) (X:Finset V):Finset (Bool×Bool×V):=
  X.image (fun x=>(j,a,x))

def markedFixedEndpoint (π:Equiv.Perm V) (j a:Bool):Equiv.Perm V:=
  if j && a then π else Equiv.refl V

def markedMovingEndpoint (π:Equiv.Perm V) (j a:Bool):Equiv.Perm V:=
  if j && !a then π else Equiv.refl V

theorem marked_same_direction_eligible (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (j a:Bool) (x z:V):
    markedRowEligible P π b (j,a,x) z↔
      ¬PermutationClose π b x z∧P.Adj (markedFixedEndpoint π j a x) (markedMovingEndpoint π j a z):=by
  cases j <;> cases a <;>
    simp [markedRowEligible,markedRowRim,markedFixedEndpoint,markedMovingEndpoint,P.adj_comm]

theorem marked_same_direction_physical (π:Equiv.Perm V) (j a:Bool) (x z:V):
    markedPairPhysical π (markedRowRim (j,a,x) z)=
      s(markedFixedEndpoint π j a x,markedMovingEndpoint π j a z):=by
  cases j <;> cases a <;>
    simp [markedPairPhysical,markedRowRim,markedFixedEndpoint,markedMovingEndpoint,Sym2.eq_swap]

theorem marked_same_direction_set_physical_injective (π:Equiv.Perm V) (j a:Bool) (X:Finset V) (z:V):
    Set.InjOn (fun e=>markedPairPhysical π (markedRowRim e z)) (markedSameDirectionSetRequests j a X):=by
  intro e he f hf h
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp he
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hf
  dsimp only at h
  rw [marked_same_direction_physical,marked_same_direction_physical] at h
  have hxy: x=y:=(markedFixedEndpoint π j a).injective (Sym2.congr_left.mp h)
  exact congrArg (fun v=>(j,a,v)) hxy

theorem marked_same_direction_set_domain_lower (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (A:Finset V) (hA:A.image π=A) (j a:Bool) (X:Finset V) (hX:X.card≤2)
    (γ:ℝ) (hγ1:γ≤1)
    (hdeg:∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ)):
    γ*A.card-2*(2*(b:ℝ)+1)≤
      ((markedRowDomain P π b A (markedSameDirectionSetRequests j a X) ∅).card:ℝ):=by
  let θ:=markedFixedEndpoint π j a
  let τ:=markedMovingEndpoint π j a
  have hτ:A.image τ=A:=by
    cases j <;> cases a <;> simp [τ,markedMovingEndpoint,hA]
  have hc:=permutedNeighbourChoices_card_lower P π τ b A (X.image θ) X γ hγ1
    ((Finset.card_image_le).trans hX) (by
      intro x hx
      rw [hτ,Finset.inter_comm]
      exact hdeg x)
  have hsub:permutedNeighbourChoices P π τ b A (X.image θ) X⊆
      markedRowDomain P π b A (markedSameDirectionSetRequests j a X) ∅:=by
    intro z hz
    obtain ⟨hzA,hzP,hzsep⟩:=Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨hzA,?_,marked_same_direction_set_physical_injective π j a X z,by simp⟩
    intro e he
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp he
    exact (marked_same_direction_eligible P π b j a x z).mpr
      ⟨hzsep x hx,hzP (θ x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩
  have hcard:((permutedNeighbourChoices P π τ b A (X.image θ) X).card:ℝ)≤
      (markedRowDomain P π b A (markedSameDirectionSetRequests j a X) ∅).card:=by
    exact_mod_cast Finset.card_le_card hsub
  have hX':(X.card:ℝ)≤2:=by exact_mod_cast hX
  have hmul:=mul_le_mul_of_nonneg_right hX' (show (0:ℝ)≤2*b+1 by positivity)
  linarith only [hc,hcard,hmul]

end Oberwolfach
