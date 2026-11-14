module

public import Oberwolfach.LongDualReferenceTypeAgreement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance dualProtectedRefDecEq : DecidableEq V := Classical.decEq V
local instance dualProtectedRefArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_dual_correction_protects_reference_types
    (G Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (Mhost:V→V→ℕ)
    (I:Finset V) (C:Finset (Finset V⊕(V×U))):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G ω Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    ∀M:Finset {e:V×V // P e},
      (∀e,e.val.1∈I→(e∈M↔e∈T₁))→
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→(e∈M↔e∈T₁))→
      ∀e:{a:V×V // P a},(e.val.1∈I ∨ Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)→
      (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω x)) false e.val.1 e.val.2=1→e∉M) ∧
      (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω x)) true e.val.1 (π.symm e.val.2)=1→e∈M):=by
  intro P T₁ M hI hC e hprotect
  have heq:e∈M↔e∈T₁:=hprotect.elim (hI e) (hC e)
  have ha:=long_dual_initial_agrees_with_selected_types G Small π d ω Mhost e
  exact ⟨fun hOrd hM=>ha.1 hOrd (heq.mp hM),fun hMark=>heq.mpr (ha.2 hMark)⟩
end Oberwolfach
