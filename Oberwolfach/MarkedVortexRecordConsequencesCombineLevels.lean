module

public import Oberwolfach.MarkedVortexPositiveRecordConsequences
public import Oberwolfach.MarkedVortexZeroRecordConsequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_record_consequences_combine_levels
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut:ℝ)
    (hPositive:MarkedVortexPositiveRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut)
    (hZero:MarkedVortexZeroRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut):
    MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut :=by
  unfold MarkedVortexPositiveRecordConsequences at hPositive
  unfold MarkedVortexZeroRecordConsequences at hZero
  unfold MarkedVortexCorrectedRecordConsequences
  rcases hPositive with ⟨p1,p2,p3,p4,p5,p6,p7,p8⟩
  rcases hZero with ⟨z1,z2,z3,z4,z5,z6,z7,z8⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    by_cases h:i=0
    · exact z1 i hi h
    · exact p1 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z2 i hi h
    · exact p2 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z3 i hi h
    · exact p3 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z4 i hi h
    · exact p4 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z5 i hi h
    · exact p5 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z6 i hi h
    · exact p6 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z7 i hi h
    · exact p7 i hi (Nat.pos_of_ne_zero h)
  · intro i hi
    by_cases h:i=0
    · exact z8 i hi h
    · exact p8 i hi (Nat.pos_of_ne_zero h)
end Oberwolfach
