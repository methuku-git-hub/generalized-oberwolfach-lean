module

public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section
/-! The potential-wheel seed keeps its original coefficient and normalization
when its vertex tuple is reindexed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z:Type} [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

theorem marked_potential_seed_relabel {m b:ℕ}
    (f:W↪V) (g:Z↪U) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (hc:∀ x,f (ρ x)=π (f x)) (weight:(Fin (m+1)→V)→ℝ) (denom:ℝ)
    (C:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd m ρ b
      (fun _ _=>True) (fun _ _=>True)) :
    let e : W×W → V×V := Prod.map f f
    let M:=markedWheelVertexEmbedding (m:=m) (b:=b)
      (tail:=Prod.fst) (head:=Prod.snd) (ktail:=Prod.fst) (khead:=Prod.snd)
      (tail':=Prod.fst) (head':=Prod.snd) (ktail':=Prod.fst) (khead':=Prod.snd)
      (H₀:=fun _ _=>True) (HK:=fun _ _=>True) (H₀':=fun _ _=>True) (HK':=fun _ _=>True)
      f g hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    weight (M C).1.val / denom = weight (f ∘ C.1.val) / denom := by
  rfl
end Oberwolfach
