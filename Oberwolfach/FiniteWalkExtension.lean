module

public import Oberwolfach.SimpleWalkIntervalConcatenation

@[expose] public section
/-! Extend a finite consecutive family of walks by stationary walks without
 changing the initial paths or their support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def finiteWalkClamp {V:Type*} {n:ℕ} (v:Fin (n+1)→V) (i:ℕ):V :=
  v ⟨min i n,by omega⟩

def finiteWalkExtension {V:Type*} {n:ℕ} (G:SimpleGraph V) (v:Fin (n+1)→V)
    (p:∀i:Fin n,G.Walk (v i.castSucc) (v i.succ)):
    ∀i:ℕ,G.Walk (finiteWalkClamp v i) (finiteWalkClamp v (i+1)) := by
  intro i
  by_cases hi:i<n
  · have h₁:v (⟨i,hi⟩:Fin n).castSucc=finiteWalkClamp v i:=by
      unfold finiteWalkClamp
      apply congrArg v
      apply Fin.ext
      simp only [Fin.val_castSucc,Fin.val_mk,Nat.min_eq_left (show i ≤ n by omega)]
    have h₂:v (⟨i,hi⟩:Fin n).succ=finiteWalkClamp v (i+1):=by
      unfold finiteWalkClamp
      apply congrArg v
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_mk,Nat.min_eq_left (show i+1 ≤ n by omega)]
    exact (p ⟨i,hi⟩).copy h₁ h₂
  · have hstay:finiteWalkClamp v i=finiteWalkClamp v (i+1):=by
      unfold finiteWalkClamp
      apply congrArg v
      apply Fin.ext
      change min i n=min (i+1) n
      rw [Nat.min_eq_right (show n ≤ i by omega),Nat.min_eq_right (show n ≤ i+1 by omega)]
    exact (SimpleGraph.Walk.nil : G.Walk (finiteWalkClamp v i) (finiteWalkClamp v i)).copy rfl hstay

theorem finite_walk_extension_initial_properties
    {V:Type*} {n:ℕ} (G:SimpleGraph V) (v:Fin (n+1)→V)
    (p:∀i:Fin n,G.Walk (v i.castSucc) (v i.succ)) (i:Fin n):
    ((finiteWalkExtension G v p i).IsPath ↔ (p i).IsPath) ∧
      (finiteWalkExtension G v p i).length=(p i).length ∧
      (finiteWalkExtension G v p i).support=(p i).support := by
  simp only [finiteWalkExtension, dif_pos i.isLt, SimpleGraph.Walk.isPath_copy,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.support_copy, and_self]
end Oberwolfach
