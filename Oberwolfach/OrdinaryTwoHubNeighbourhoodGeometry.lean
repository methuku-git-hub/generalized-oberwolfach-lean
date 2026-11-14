module

public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.OrdinaryLocalDeletion

@[expose] public section
/-! Two-hub common-neighbour lower bounds from the fixed raw row event.
The loss from deleting conflict edges is counted in the realised graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_two_hub_neighbourhood_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p:ℝ) (s:U→Color→ℝ) (j:Color) (γ lam t L:ℝ)
    (hγ:0≤γ) (hlam:0≤lam) (hL:0≤L)
    (hF:∀ v,(F.degree v:ℝ)≤L)
    (hP:∀ v w,γ*Fintype.card V≤((P.neighborFinset v∩P.neighborFinset w).card:ℝ))
    (hden:∀ (S:Finset V) (J:Finset U),S.card≤2→J.card≤2→
      lam≤p^S.card*(∏ u∈J,s u j))
    (hrows:RawOrdinaryRows P π d 2 Finset.univ p s j t σ):
    ∀ u u' v w,
      lam*γ*Fintype.card V-t-2*L≤
        (((Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u'))∩
          (rawWheelGraph P σ\F).neighborFinset v∩(rawWheelGraph P σ\F).neighborFinset w).card:ℝ) := by
  intro u u' v w
  let S:Finset V:={v,w}
  let J:Finset U:={u,u'}
  let T:=Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u')
  have hS:S.card≤2:=by
    dsimp [S]
    have hh:=Finset.card_insert_le v ({w}:Finset V)
    simpa using hh
  have hJ:J.card≤2:=by
    dsimp [J]
    have hh:=Finset.card_insert_le u ({u'}:Finset U)
    simpa using hh
  have htest:=hrows S J hS hJ
  have hden':lam≤p^S.card*(∏ u∈J,s u j):=hden S J hS hJ
  have hraw:common (common Finset.univ S (fun x=>(rawWheelGraph P σ).neighborFinset x)) J
        (fun u=>Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u))=
      common T S (fun x=>(rawWheelGraph P σ).neighborFinset x) := by
    ext z
    simp only [mem_common_iff,Finset.mem_univ,true_and,Finset.mem_filter]
    simp [S,J,T] <;> tauto
  have hparent:common Finset.univ S (fun x=>P.neighborFinset x)=
      P.neighborFinset v∩P.neighborFinset w := by
    ext z
    simp only [mem_common_iff,Finset.mem_univ,true_and]
    simp [S] <;> tauto
  have htarget:common T S (fun x=>(rawWheelGraph P σ\F).neighborFinset x)=
      T∩(rawWheelGraph P σ\F).neighborFinset v∩(rawWheelGraph P σ\F).neighborFinset w := by
    ext z
    simp only [mem_common_iff,Finset.mem_inter]
    simp [S] <;> tauto
  rw [hraw,hparent] at htest
  have hloss:=ordinary_common_sdiff_bound (rawWheelGraph P σ) F T S L hF
  rw [htarget] at hloss
  have hSreal:(S.card:ℝ)≤2:=by exact_mod_cast hS
  have hmul:lam*(γ*Fintype.card V)≤
      (p^S.card*(∏ u∈J,s u j))*((P.neighborFinset v∩P.neighborFinset w).card:ℝ):=
    mul_le_mul hden' (hP v w) (by positivity) (hlam.trans hden')
  have ht1 := (abs_lt.mp htest).1
  have ht2 := (abs_le.mp hloss).1
  have hSL:(S.card:ℝ)*L≤2*L:=mul_le_mul_of_nonneg_right hSreal hL
  nlinarith only [hmul,ht1,ht2,hSL]
end Oberwolfach
