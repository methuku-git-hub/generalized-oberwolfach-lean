module

public import Oberwolfach.MarkedReferenceLevelChain

@[expose] public section

/-! Nested embeddings place the terminal pair inside the first protected
pair. No additional size, sampling or host assumption is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
variable (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
variable [∀ i,Fintype (levels i).VP] [∀ i,Fintype (levels i).UP]
  [∀ i,LinearOrder (levels i).VP] [∀ i,DecidableEq (levels i).UP]
variable {count:ℕ} (chain:MarkedReferenceLevelChain levels count)

theorem marked_reference_level_in_first_pair (i:ℕ) (hi:0 < i) (hic:i < count):
    (∀ v,chain.intoV i v∈(levels 0).I) ∧ (∀ u,chain.intoU i u∈(levels 0).J):=by
  induction i with
  | zero => omega
  | succ i ih =>
    have hnext:i+1<count:=by omega
    constructor
    · intro v
      rw [chain.composeV i hnext v]
      by_cases hzero:i=0
      · subst i
        rw [chain.firstV,←chain.nextVimage 0 hnext]
        exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
      · exact (ih (by omega) (by omega)).1 (chain.nextV i hnext v)
    · intro u
      rw [chain.composeU i hnext u]
      by_cases hzero:i=0
      · subst i
        rw [chain.firstU,←chain.nextUimage 0 hnext]
        exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
      · exact (ih (by omega) (by omega)).2 (chain.nextU i hnext u)

theorem marked_reference_terminal_pair_in_first_pair (hcount:0<count):
    ((levels (count-1)).I.image (chain.intoV (count-1)))⊆(levels 0).I ∧
    ((levels (count-1)).J.image (chain.intoU (count-1)))⊆(levels 0).J:=by
  by_cases hOne:count=1
  · subst count
    constructor <;> intro x hx <;> obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
    · simpa only [Nat.sub_self,chain.firstV] using hv
    · simpa only [Nat.sub_self,chain.firstU] using hv
  · have hpos:0<count-1:=by omega
    have hlt:count-1<count:=by omega
    obtain ⟨hv,hu⟩:=marked_reference_level_in_first_pair levels chain (count-1) hpos hlt
    constructor <;> intro x hx <;> obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hx
    · exact hv v
    · exact hu v

end Oberwolfach
