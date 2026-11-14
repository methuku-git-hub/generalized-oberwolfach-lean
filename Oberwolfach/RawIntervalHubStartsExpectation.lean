module

public import Oberwolfach.RawIntervalNeighbourCounts

@[expose] public section
/-! The number of raw intervals of a prescribed colour in each hub column. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalFamilyStartState (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (a:V×U):Bool :=
  if rawIntervalColouredStart π d (fun e=>σ (a.2,e)) a.1 g then true else false

theorem rawIntervalFamilyStartState_supported (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ τ:RawIntervalFamilyOutcome V U Γ Color) (a:V×U)
    (ha:∀ e∈rawIntervalFamilyCoordinates π d a,σ e=τ e):
    rawIntervalFamilyStartState π d g σ a=rawIntervalFamilyStartState π d g τ a := by
  have hloc:∀ e∈rawIntervalStateCoordinates π d a.1,σ (a.2,e)=τ (a.2,e):=by
    intro e he; exact ha (a.2,e) (Finset.mem_image.mpr ⟨e,he,rfl⟩)
  have hact (x:V) (hx:x∈permutationWindow π (2*d) d a.1):
      σ (a.2,Sum.inl x)=τ (a.2,Sum.inl x):=by
    apply hloc
    simp only [rawIntervalStateCoordinates,Finset.mem_union,Finset.mem_image,Finset.mem_singleton]
    exact Or.inl (Or.inl ⟨x,hx,rfl⟩)
  have hstart:σ (a.2,Sum.inr (Sum.inl a.1))=τ (a.2,Sum.inr (Sum.inl a.1)):=by
    apply hloc
    simp only [rawIntervalStateCoordinates,Finset.mem_union,Finset.mem_image,Finset.mem_singleton]
    exact Or.inl (Or.inr ⟨a.1,permutationWindow_self π d 0 a.1,rfl⟩)
  have hself:=hact a.1 (permutationWindow_self π (2*d) d a.1)
  unfold rawIntervalFamilyStartState
  congr 1
  apply propext
  dsimp only [rawIntervalColouredStart,rawIntervalKept]
  rw [hself,hstart]
  apply and_congr_left
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  apply forall_congr'
  intro _
  exact Iff.of_eq (congrArg (fun b=>b=false) (hact x (permutationWindow_mono π (by omega) (by omega) a.1 hx)))

end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalHubStartCount (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U):ℝ :=
  ∑ v:V,if rawIntervalFamilyStartState π d g σ (v,u) then 1 else 0

theorem rawIntervalHubStartCount_pattern (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U):
    rawIntervalHubStartCount π d g σ u =
      supportedPatternSum (fun v:V=>{v}×ˢ{u}) (fun _=>1)
        (fun _ _=>true) (rawIntervalFamilyStartState π d g) σ := by
  unfold rawIntervalHubStartCount supportedPatternSum
  simp_rw [patternValue_indicator,one_mul]
  apply Finset.sum_congr rfl
  intro v _
  simp

theorem hub_start_pattern_square_sum (u:U) :
    (∑ a:V×U,(∑ v:V,if a∈{v}×ˢ{u} then (1:ℝ) else 0)^2)≤Fintype.card V:=by
  have hh:=neighbour_pattern_square_sum (Finset.univ:Finset V) ({u}:Finset U)
  simpa using hh

variable (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalHubStartCount_expectation
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (u:U) (g:Γ):
    (FiniteLaw.pi μfamily).expectation (fun σ=>rawIntervalHubStartCount π d g σ u)=
      (Fintype.card V:ℝ)*q u g/d := by
  unfold FiniteLaw.expectation rawIntervalHubStartCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (v:V):
      (∑ σ,(FiniteLaw.pi μfamily).mass σ * (if rawIntervalFamilyStartState π d g σ (v,u) then (1:ℝ) else 0))=q u g/d:=by
    have hh:=rawIntervalFamily_column_event d hd q hq hQ s hs hS u
      (fun τ=>rawIntervalColouredStart π d τ v g)
    rw [rawIntervalColouredStart_probability π d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u) hnoshort v g] at hh
    unfold FiniteLaw.probability at hh
    simpa [rawIntervalFamilyStartState,mul_ite] using hh
  simp_rw [h]
  simp [Finset.sum_const,nsmul_eq_mul]
  ring


end Oberwolfach
