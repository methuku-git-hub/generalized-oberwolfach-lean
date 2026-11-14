module

public import Oberwolfach.RawIntervalHubStartsExpectation

@[expose] public section
/-! Identify the real-valued count with the cardinality of the actual set
of raw starts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem rawIntervalHubStartCount_card (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U):
    rawIntervalHubStartCount π d g σ u =
    ((Finset.univ.filter (fun v:V=>rawIntervalColouredStart π d (fun e=>σ (u,e)) v g)).card:ℝ) := by
  unfold rawIntervalHubStartCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  simp only [rawIntervalFamilyStartState]
  split_ifs <;> simp_all
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalHubFamily (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U):Finset (Finset V):=
  (Finset.univ.filter (fun v:V=>rawIntervalColouredStart π d (fun e=>σ (u,e)) v g)).image
    (fun v=>permutationWindow π 0 (d-1) v)

theorem rawIntervalHubFamily_card (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U):
    (rawIntervalHubFamily π d g σ u).card=(Finset.univ.filter
      (fun v:V=>rawIntervalColouredStart π d (fun e=>σ (u,e)) v g)).card := by
  unfold rawIntervalHubFamily
  apply Finset.card_image_iff.mpr
  intro a ha b hb heq
  have ha':= (Finset.mem_filter.mp ha).2
  have hb':= (Finset.mem_filter.mp hb).2
  have hax:a∈permutationWindow π 0 (d-1) a:=permutationWindow_self π 0 (d-1) a
  change permutationWindow π 0 (d-1) a=permutationWindow π 0 (d-1) b at heq
  have hbx:a∈permutationWindow π 0 (d-1) b:=by rw [←heq];exact hax
  have haext:a∈permutationWindow π 0 d a:=permutationWindow_self π 0 d a
  have hbext:a∈permutationWindow π 0 d b:=permutationWindow_mono π (by omega) (by omega) b hbx
  exact (rawInterval_coloured_start_unique π d (fun e=>σ (u,e)) a a b g g ha' hb' haext hbext).1

end Oberwolfach
