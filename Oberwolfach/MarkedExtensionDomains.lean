module

public import Oberwolfach.MarkedRowCounts
public import Oberwolfach.PermutedNeighbourChoices

@[expose] public section

/-! The four concrete one- and two-edge requests in marked cover-down.
The head of the incoming marked edge is pi(w). Physical edge distinctness
is proved from the appropriate exclusion on the two fixed endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

def markedOneExtensionRequests (j : Bool) (v : V) : Finset (Bool×Bool×V) := {(j,false,v)}
def markedTwoExtensionRequests (j : Bool) (v w : V) : Finset (Bool×Bool×V) :=
  {(false,false,v),(j,true,w)}

theorem marked_two_extension_physical_injective (π : Equiv.Perm V) (j : Bool) (v w z : V)
    (hne : v≠if j then π w else w) :
    Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a z)) (markedTwoExtensionRequests j v w) := by
  have hp : markedPairPhysical π (markedRowRim (false,false,v) z)≠
      markedPairPhysical π (markedRowRim (j,true,w) z) := by
    intro he
    have he' : s(v,z)=s(z,if j then π w else w) := by
      cases j <;> simpa [markedPairPhysical,markedRowRim] using he
    have hh : s(v,z)=s((if j then π w else w),z) := he'.trans Sym2.eq_swap
    exact hne (Sym2.congr_left.mp hh)
  intro a ha b hb he
  simp only [markedTwoExtensionRequests,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · rfl
  · exact False.elim (hp he)
  · exact False.elim (hp he.symm)
  · rfl

theorem marked_one_extension_domain_lower (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : Finset V) (hA : A.image π=A) (j : Bool) (v : V) (γ : ℝ) (hγ1 : γ≤1)
    (hdeg : ∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ)) :
    γ*A.card-(2*(b:ℝ)+1)≤
      ((markedRowDomain P π b A (markedOneExtensionRequests j v) ∅).card:ℝ) := by
  let τ : Equiv.Perm V:=if j then π else Equiv.refl V
  have hτ : A.image τ=A := by cases j <;> simp [τ,hA]
  have hc:=permutedNeighbourChoices_card_lower P π τ b A {v} {v} γ hγ1 (by simp)
    (by intro x hx;rw [hτ,Finset.inter_comm];exact hdeg x)
  have hsub : permutedNeighbourChoices P π τ b A {v} {v}⊆
      markedRowDomain P π b A (markedOneExtensionRequests j v) ∅ := by
    intro z hz
    obtain ⟨hzA,hzP,hzsep⟩:=Finset.mem_filter.mp hz
    have hp:=hzP v (by simp)
    have hs:=hzsep v (by simp)
    apply Finset.mem_filter.mpr
    refine ⟨hzA,?_,?_,by simp⟩
    · intro a ha
      simp only [markedOneExtensionRequests,Finset.mem_singleton] at ha
      subst a
      cases j <;> simpa [markedRowEligible,markedRowRim,τ] using And.intro hs hp
    · intro a ha c hc he
      have ha' : a=(j,false,v) := by simpa [markedOneExtensionRequests] using ha
      have hc' : c=(j,false,v) := by simpa [markedOneExtensionRequests] using hc
      exact ha'.trans hc'.symm
  have hh : ((permutedNeighbourChoices P π τ b A {v} {v}).card:ℝ)≤
      (markedRowDomain P π b A (markedOneExtensionRequests j v) ∅).card := by
    exact_mod_cast Finset.card_le_card hsub
  simpa using hc.trans hh

theorem marked_two_extension_domain_lower (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : Finset V) (j : Bool) (v w : V) (hne : v≠if j then π w else w)
    (γ : ℝ) (hγ1 : γ≤1)
    (hdeg : ∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ)) :
    γ*A.card-2*(2*(b:ℝ)+1)≤
      ((markedRowDomain P π b A (markedTwoExtensionRequests j v w) ∅).card:ℝ) := by
  let w' := if j then π w else w
  have hR : ({v,w'}:Finset V).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
  have hc:=permutedNeighbourChoices_card_lower P π (Equiv.refl V) b A {v,w'} {v,w} γ hγ1 hR
    (by intro x hx;simpa [Finset.inter_comm] using hdeg x)
  have hsub : permutedNeighbourChoices P π (Equiv.refl V) b A {v,w'} {v,w}⊆
      markedRowDomain P π b A (markedTwoExtensionRequests j v w) ∅ := by
    intro z hz
    obtain ⟨hzA,hzP,hzsep⟩:=Finset.mem_filter.mp hz
    have hvP : P.Adj v z:=hzP v (by simp)
    have hwP : P.Adj w' z:=hzP w' (by simp)
    have hvsep:=hzsep v (by simp)
    have hwsep:=hzsep w (by simp)
    apply Finset.mem_filter.mpr
    refine ⟨hzA,?_,marked_two_extension_physical_injective π j v w z hne,by simp⟩
    intro a ha
    simp only [markedTwoExtensionRequests,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl
    · simpa [markedRowEligible,markedRowRim] using And.intro hvsep hvP
    · cases j <;> simpa [markedRowEligible,markedRowRim,w'] using And.intro hwsep hwP.symm
  have hpair : (({v,w}:Finset V).card:ℝ)≤2 := by
    exact_mod_cast (Finset.card_insert_le v ({w}:Finset V)).trans (by simp : ({w}:Finset V).card+1≤2)
  have hloss:=mul_le_mul_of_nonneg_right hpair (by positivity : (0:ℝ)≤2*b+1)
  have hcard : ((permutedNeighbourChoices P π (Equiv.refl V) b A {v,w'} {v,w}).card:ℝ)≤
      (markedRowDomain P π b A (markedTwoExtensionRequests j v w) ∅).card := by exact_mod_cast Finset.card_le_card hsub
  linarith only [hc,hloss,hcard]

end Oberwolfach
