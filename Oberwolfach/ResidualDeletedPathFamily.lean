module

public import Oberwolfach.ResidualSegmentChoiceExtension

@[expose] public section
/-! Index the actual final paths and maximal selected-run subpaths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

def SelectedRunIndex (s₂:Finset I) (d:ℕ) (T:I→Finset ℕ) :=
  Σ i : {i // i∈s₂}, {r : ℕ×ℕ // r∈selectedSegmentRuns d (T i.1)}

def DeletedPathIndex (s₁ s₂:Finset I) (d:ℕ) (T:I→Finset ℕ) :=
  {i // i∈s₁} ⊕ SelectedRunIndex s₂ d T

def deletedPathStart (F:SimpleGraph V) (s₁ s₂:Finset I) (u v:I→V)
    (P:∀i,F.Walk (u i) (v i)) (c d:ℕ) (T:I→Finset ℕ):
    DeletedPathIndex s₁ s₂ d T→V
  | .inl i => (P i.1).getVert 2
  | .inr ⟨i,r⟩ => (P i.1).getVert (2+c*r.1.1)

def deletedPathEnd (F:SimpleGraph V) (s₁ s₂:Finset I) (u v:I→V)
    (P:∀i,F.Walk (u i) (v i)) (c d:ℕ) (T:I→Finset ℕ):
    DeletedPathIndex s₁ s₂ d T→V
  | .inl i => (P i.1).getVert (2+c*d)
  | .inr ⟨i,r⟩ => (P i.1).getVert (2+c*(r.1.2+1))

def deletedPathWalk (F:SimpleGraph V) (s₁ s₂:Finset I) (u v:I→V)
    (P:∀i,F.Walk (u i) (v i)) (c d:ℕ) (T:I→Finset ℕ)
    (hT:∀i∈s₂,T i⊆Finset.range d):
    ∀ z:DeletedPathIndex s₁ s₂ d T,
      F.Walk (deletedPathStart F s₁ s₂ u v P c d T z)
        (deletedPathEnd F s₁ s₂ u v P c d T z)
  | .inl i => walkInterval (P i.1) 2 (2+c*d) (by omega)
  | .inr ⟨i,r⟩ => selectedRunWalk (P i.1) c r.1.1 r.1.2
      ((selected_run_mem d (T i.1) (hT i.1 i.2) r.1.1 r.1.2).mp r.2).1
end Oberwolfach
