module

public import Oberwolfach.MarkedInitialPaths

@[expose] public section

/-! Size, root avoidance and pair separation for the actual union of the
rim and spoke path vertices. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A S:Type} [Fintype A] [Fintype S] [DecidableEq V]

def markedPathUnion (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V):Finset V:=
  (Finset.univ.biUnion (fun e=>Finset.univ.image (pr e)))∪
    (Finset.univ.biUnion (fun e=>Finset.univ.image (ps e)))

theorem markedPathUnion_rim (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V) (e:A) (k:Fin r):
    pr e k∈markedPathUnion r s pr ps:=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩)

theorem markedPathUnion_spoke (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V) (e:S) (k:Fin s):
    ps e k∈markedPathUnion r s pr ps:=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩)

theorem markedPathUnion_card (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V):
    (markedPathUnion r s pr ps).card≤Fintype.card A*r+Fintype.card S*s:=by
  have bound {J:Type} [Fintype J] (n:ℕ) (p:J→Fin n→V):
      (Finset.univ.biUnion (fun j=>Finset.univ.image (p j))).card≤Fintype.card J*n:=by
    calc
      _≤∑ j:J,(Finset.univ.image (p j)).card:=Finset.card_biUnion_le
      _≤∑ _:J,n:=Finset.sum_le_sum (fun j _=>by simpa using Finset.card_image_le (f:=p j) (s:=Finset.univ))
      _=Fintype.card J*n:=by simp
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (bound r pr) (bound s ps))

theorem markedPathUnion_avoid (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V) (Z:Finset V)
    (hr:∀ e k,pr e k∉Z) (hs:∀ e k,ps e k∉Z):
    Disjoint (markedPathUnion r s pr ps) Z:=by
  apply Finset.disjoint_left.mpr
  intro x hx hz
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨e,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    exact hr e k hz
  · obtain ⟨e,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    exact hs e k hz

theorem markedPathUnion_root_separated (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V)
    (π:Equiv.Perm V) (b:ℕ) (Z:Finset V)
    (hr:∀ e k,∀ z∈Z,¬PermutationClose π b (pr e k) z)
    (hs:∀ e k,∀ z∈Z,¬PermutationClose π b (ps e k) z):
    ∀ x∈markedPathUnion r s pr ps,∀ z∈Z,¬PermutationClose π b x z:=by
  intro x hx z hz
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨e,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    exact hr e k z hz
  · obtain ⟨e,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    exact hs e k z hz

theorem markedPathUnion_separated (r s:ℕ) (pr:A→Fin r→V) (ps:S→Fin s→V)
    (π:Equiv.Perm V) (b:ℕ)
    (hr:∀ e f k z,pr e k≠pr f z→¬PermutationClose π b (pr e k) (pr f z))
    (hs:∀ e f k z,ps e k≠ps f z→¬PermutationClose π b (ps e k) (ps f z))
    (hrs:∀ e f k z,¬PermutationClose π b (pr e k) (ps f z)):
    ∀ x∈markedPathUnion r s pr ps,∀ y∈markedPathUnion r s pr ps,x≠y→¬PermutationClose π b x y:=by
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
  all_goals obtain ⟨e,_,hx⟩:=Finset.mem_biUnion.mp hx
  all_goals obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
  all_goals obtain ⟨f,_,hy⟩:=Finset.mem_biUnion.mp hy
  all_goals obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp hy
  · exact hr e f k z hxy
  · exact hrs e f k z
  · exact fun hc=>hrs f e z k ((permutationClose_symm π b _ _).mp hc)
  · exact hs e f k z hxy

end Oberwolfach
