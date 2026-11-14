module

public import Oberwolfach.OrdinaryDomainNeighbourhoodEvent

@[expose] public section
/-! Single-root rim and spoke profiles are included in the existing common
neighbourhood event on the two fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_sampled_single_root_profiles
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (J:Finset U)
    (pR pH tR tH:ℝ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hrows:RawOrdinaryRows P π d 2 I pR s j tR σ)
    (hcols:RawOrdinaryDomainIndices F π d 3 J pH j tH σ):
    (∀v,|(((rawWheelGraph P σ).neighborFinset v∩I).card:ℝ)-
      pR*(P.neighborFinset v∩I).card|<tR) ∧
    (∀v,|((J.filter (rawWheelSpokes π d σ j v)).card:ℝ)-pH*J.card|<tH):=by
  constructor
  · intro v
    have hh:=hrows {v} ∅ (by simp) (by simp)
    have he (A:Finset V) (N:V→Finset V):common A {v} N=N v∩A:=by
      ext w;simp [common,Finset.mem_inter];tauto
    have h0 (A:Finset V) (N:U→Finset V):common A (∅:Finset U) N=A:=by
      ext w;simp [common]
    rw [h0,he,he] at hh
    simpa only [Finset.card_singleton,Finset.prod_empty,pow_one,mul_one] using hh
  · intro v
    have hh:=hcols {v} (by simp) (by intro x hx y hy;simp only [Finset.mem_singleton] at hx hy;subst x;subst y;exact fun h=>F.irrefl h)
    have he:common J {v} (fun x=>Finset.univ.filter (rawWheelSpokes π d σ j x))=
        J.filter (rawWheelSpokes π d σ j v):=by
      ext u;simp [common]
    rw [he] at hh
    simpa only [Finset.card_singleton,pow_one] using hh
end Oberwolfach
