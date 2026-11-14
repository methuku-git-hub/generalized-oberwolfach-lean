module

public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.OrdinaryLocalDeletion

@[expose] public section
/-! Root-set common-neighbour bounds from the original row event, with
realised conflict-edge deletion losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_many_root_two_hub_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:2≤h) (σ:RawWheelOutcome V U Γ Color)
    (p:ℝ) (s:U→Color→ℝ) (j:Color) (γ lam t L:ℝ)
    (hγ:0≤γ) (hlam:0≤lam) (hL:0≤L)
    (hF:∀ v,(F.degree v:ℝ)≤L)
    (hP:∀ (S:Finset V),S.card≤h→γ*Fintype.card V≤
      ((common Finset.univ S (fun v=>P.neighborFinset v)).card:ℝ))
    (hden:∀ (S:Finset V) (J:Finset U),S.card≤h→J.card≤h→
      lam≤p^S.card*(∏ u∈J,s u j))
    (hrows:RawOrdinaryRows P π d h Finset.univ p s j t σ):
    ∀ u u' (S:Finset V),S.card≤h→
      lam*γ*Fintype.card V-t-h*L≤
        ((common (Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u')) S
          (fun x=>(rawWheelGraph P σ\F).neighborFinset x)).card:ℝ) := by
  intro u u' S hS
  let J:Finset U:={u,u'}
  let T:=Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u')
  have hJ:J.card≤h:=by
    have hJ2:J.card≤2:=by dsimp [J];have hx:=Finset.card_insert_le u ({u'}:Finset U);simpa using hx
    omega
  have htest:=hrows S J hS hJ
  have hden':lam≤p^S.card*(∏ u∈J,s u j):=hden S J hS hJ
  have hraw:common (common Finset.univ S (fun x=>(rawWheelGraph P σ).neighborFinset x)) J
        (fun u=>Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u))=
      common T S (fun x=>(rawWheelGraph P σ).neighborFinset x) := by
    ext z
    simp only [mem_common_iff,Finset.mem_univ,true_and,Finset.mem_filter]
    simp [J,T] <;> tauto
  rw [hraw] at htest
  have hloss:=ordinary_common_sdiff_bound (rawWheelGraph P σ) F T S L hF
  have hSreal:(S.card:ℝ)≤h:=by exact_mod_cast hS
  have hmul:lam*(γ*Fintype.card V)≤
      (p^S.card*(∏ u∈J,s u j))*((common Finset.univ S (fun v=>P.neighborFinset v)).card:ℝ):=
    mul_le_mul hden' (hP S hS) (by positivity) (hlam.trans hden')
  have ht1:=(abs_lt.mp htest).1
  have ht2:=(abs_le.mp hloss).1
  have hSL:(S.card:ℝ)*L≤h*L:=mul_le_mul_of_nonneg_right hSreal hL
  nlinarith only [hmul,ht1,ht2,hSL]
end Oberwolfach
