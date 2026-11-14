module

public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.RawOrdinaryDomainIndexEvent

@[expose] public section
/-! The singleton tests in the original full-domain common event give all
rim, spoke-row and spoke-column degree bounds for the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_raw_global_degree_from_profiles
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (pR pH tR tH:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (hs:∀u,s u j=pH)
    (hrows:RawOrdinaryRows P π d 3 Finset.univ pR s j tR raw)
    (hindices:RawOrdinaryDomainIndices F π d 3 Finset.univ pH j tH raw):
    (∀v,((rawWheelGraph P raw).degree v:ℝ)≤pR*(P.degree v)+tR) ∧
    (∀v,((Finset.univ.filter (rawWheelSpokes π d raw j v)).card:ℝ)≤pH*Fintype.card U+tH) ∧
    (∀u,((Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u)).card:ℝ)≤pH*Fintype.card V+tR):=by
  have hcommon (G:SimpleGraph V) (v:V):common Finset.univ {v} (fun x=>G.neighborFinset x)=G.neighborFinset v:=by
    ext x
    simp [mem_common_iff]
  have hempty (A:Finset V):common A (∅:Finset U) (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))=A:=by
    ext x
    simp [mem_common_iff]
  constructor
  · intro v
    have hh:=hrows {v} ∅ (by simp) (by simp)
    rw [hcommon,hempty,hcommon] at hh
    simp only [Finset.card_singleton,Finset.prod_empty,pow_one,mul_one,
      SimpleGraph.card_neighborFinset_eq_degree] at hh
    linarith only [(abs_lt.mp hh).2]
  constructor
  · intro v
    have hf:∀a∈({v}:Finset V),∀b∈({v}:Finset V),¬F.Adj a b:=by
      intro a ha b hb
      simp only [Finset.mem_singleton] at ha hb
      subst a;subst b
      exact F.irrefl
    have hh:=hindices {v} (by simp) hf
    have he:common Finset.univ {v} (fun x=>Finset.univ.filter (rawWheelSpokes π d raw j x))=
        Finset.univ.filter (rawWheelSpokes π d raw j v):=by
      ext u
      simp [mem_common_iff]
    rw [he] at hh
    simp only [Finset.card_singleton,pow_one,Finset.card_univ] at hh
    linarith only [(abs_lt.mp hh).2]
  · intro u
    have hh:=hrows ∅ {u} (by simp) (by simp)
    have he:common (common Finset.univ (∅:Finset V) (fun x=>(rawWheelGraph P raw).neighborFinset x)) {u}
        (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))=
        Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u):=by
      ext v
      simp [mem_common_iff]
    have he':common Finset.univ (∅:Finset V) (fun x=>P.neighborFinset x)=(Finset.univ:Finset V):=by
      ext v
      simp [mem_common_iff]
    rw [he,he'] at hh
    simp only [Finset.card_empty,pow_zero,Finset.prod_singleton,hs,Finset.card_univ,one_mul] at hh
    linarith only [(abs_lt.mp hh).2]
end Oberwolfach
