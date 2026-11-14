module

public import Oberwolfach.MarkedReferenceActiveEndpointBase

@[expose] public section
/-! Record-scale endpoint errors on the fixed active vertex and hub sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_active_endpoint_record_inputs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (B:Finset U)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (e x:ℝ)
    (he:0≤e) (hex:e≤x/2) (hUV:Fintype.card U≤Fintype.card V)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrow:MarkedRowsWithSpokes P π d h A p k q s g j (e*A.card) σ H)
    (hidx:MarkedIndicesWithSpokes π d h B q s g j (e*B.card) σ H):
    ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card V ∧ errI≤(x/2)*Fintype.card V ∧
      MarkedRowsWithSpokes P π d h A p k q s g j errR σ H ∧
      MarkedIndicesWithSpokes π d h B q s g j errI σ H:=by
  refine ⟨e*A.card,e*B.card,by positivity,by positivity,?_,?_,hrow,hidx⟩
  · exact (mul_le_mul_of_nonneg_left (show (A.card:ℝ)≤Fintype.card V by exact_mod_cast (Finset.card_le_univ A)) he).trans
      (mul_le_mul_of_nonneg_right hex (Nat.cast_nonneg _))
  · have hB:(B.card:ℝ)≤Fintype.card V:=by exact_mod_cast (le_trans (Finset.card_le_univ B) hUV)
    exact (mul_le_mul_of_nonneg_left hB he).trans (mul_le_mul_of_nonneg_right hex (Nat.cast_nonneg _))
end Oberwolfach
