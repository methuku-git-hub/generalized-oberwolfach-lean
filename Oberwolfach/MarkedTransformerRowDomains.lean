module

public import Oberwolfach.MarkedExtensionDomains

@[expose] public section

/-! The two same-direction requests used at transformer attachments.
Incoming marked arcs have physical neighbours pi(v) and pi(w), whereas
outgoing marked requests use the inverse-image parent domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

 def markedSameDirectionRequests (j o:Bool) (v w:V):Finset (Bool×Bool×V):=
  {(j,o,v),(j,o,w)}

 theorem marked_same_direction_physical_injective (π:Equiv.Perm V) (j o:Bool)
    (v w z:V) (hne:v≠w):
    Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a z)) (markedSameDirectionRequests j o v w):=by
  have hp:markedPairPhysical π (markedRowRim (j,o,v) z)≠
      markedPairPhysical π (markedRowRim (j,o,w) z):=by
    intro he
    cases j <;> cases o
    · exact hne (Sym2.congr_left.mp he)
    · exact hne (Sym2.congr_right.mp he)
    · exact hne (Sym2.congr_left.mp he)
    · exact hne (π.injective (Sym2.congr_right.mp he))
  intro a ha b hb he
  simp only [markedSameDirectionRequests,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · rfl
  · exact (hp he).elim
  · exact (hp he.symm).elim
  · rfl

 theorem marked_same_direction_domain_lower (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (A:Finset V) (hA:A.image π=A) (j o:Bool) (v w:V) (hne:v≠w)
    (γ:ℝ) (hγ1:γ≤1)
    (hdeg:∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ)):
    γ*A.card-2*(2*(b:ℝ)+1)≤
      ((markedRowDomain P π b A (markedSameDirectionRequests j o v w) ∅).card:ℝ):=by
  let τ:Equiv.Perm V:=if j && !o then π else Equiv.refl V
  let f:V→V:=fun x=>if j && o then π x else x
  have hτ:A.image τ=A:=by cases j <;> cases o <;> simp [τ,hA]
  have hR:({f v,f w}:Finset V).card≤2:=(Finset.card_insert_le _ _).trans (by simp)
  have hc:=permutedNeighbourChoices_card_lower P π τ b A {f v,f w} {v,w} γ hγ1 hR
    (by intro x hx;rw [hτ,Finset.inter_comm];exact hdeg x)
  have hsub:permutedNeighbourChoices P π τ b A {f v,f w} {v,w}⊆
      markedRowDomain P π b A (markedSameDirectionRequests j o v w) ∅:=by
    intro z hz
    obtain ⟨hzA,hzP,hzsep⟩:=Finset.mem_filter.mp hz
    have hvP:=hzP (f v) (by simp)
    have hwP:=hzP (f w) (by simp)
    have hvsep:=hzsep v (by simp)
    have hwsep:=hzsep w (by simp)
    apply Finset.mem_filter.mpr
    refine ⟨hzA,?_,marked_same_direction_physical_injective π j o v w z hne,by simp⟩
    intro a ha
    simp only [markedSameDirectionRequests,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl
    · cases j <;> cases o <;>
        simpa [markedRowEligible,markedRowRim,τ,f] using
          And.intro hvsep (by first | exact hvP | exact hvP.symm)
    · cases j <;> cases o <;>
        simpa [markedRowEligible,markedRowRim,τ,f] using
          And.intro hwsep (by first | exact hwP | exact hwP.symm)
  have hpair:(({v,w}:Finset V).card:ℝ)≤2:=by
    exact_mod_cast (Finset.card_insert_le v ({w}:Finset V)).trans (by simp)
  have hloss:=mul_le_mul_of_nonneg_right hpair (by positivity : (0:ℝ)≤2*b+1)
  have hcard:((permutedNeighbourChoices P π τ b A {f v,f w} {v,w}).card:ℝ)≤
      (markedRowDomain P π b A (markedSameDirectionRequests j o v w) ∅).card:=by
    exact_mod_cast Finset.card_le_card hsub
  linarith only [hc,hloss,hcard]

end Oberwolfach
