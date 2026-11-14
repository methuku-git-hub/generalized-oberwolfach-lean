module

public import Oberwolfach.RootSeparatedCyclePacking

@[expose] public section
/-! Removing vertex-disjoint rooted cycles preserves divisibility of the
remaining fresh set when the root set and fresh set have divisible size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem root_packing_remaining_divisible {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (S T:Finset V) (M:Finset (OrdinaryCycle G r))
    (hpart:S∪T=Finset.univ) (hdis:Disjoint S T)
    (hS:r∣S.card) (hT:r∣T.card)
    (hpack:∀ C∈M,∀ E∈M,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E))
    (hcover:T⊆M.biUnion (ordinaryCycleVertices G r)):
    r∣(S\M.biUnion (ordinaryCycleVertices G r)).card:=by
  let U:=M.biUnion (ordinaryCycleVertices G r)
  have hU:U.card=M.card*r:=by
    dsimp [U]
    rw [Finset.card_biUnion (by intro C hC E hE hne;exact hpack C hC E hE hne)]
    simp [ordinaryCycleVertices_card]
  have hTU:T⊆U:=hcover
  have hUdiv:r∣U.card:=by rw [hU];exact dvd_mul_left _ _
  have hUT:U\T=U∩S:=by
    ext v
    have hv:v∈S∨v∈T:=by
      have hh: v∈S∪T:=by rw [hpart];exact Finset.mem_univ _
      exact Finset.mem_union.mp hh
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    constructor
    · rintro ⟨hu,hnt⟩
      rcases hv with hs|ht
      · exact ⟨hu,hs⟩
      · exact (hnt ht).elim
    · rintro ⟨hu,hs⟩
      exact ⟨hu,fun ht=>(Finset.disjoint_left.mp hdis) hs ht⟩
  have hinside:r∣(S∩U).card:=by
    have hh:r∣U.card-T.card:=Nat.dvd_sub hUdiv hT
    rw [←Finset.card_sdiff_of_subset hTU,hUT,Finset.inter_comm] at hh
    exact hh
  have he:(S\U).card=S.card-(S∩U).card:=by simpa only [Finset.inter_comm] using (Finset.card_sdiff (s:=U) (t:=S))
  rw [he]
  exact Nat.dvd_sub hS hinside
end Oberwolfach
