module

public import Oberwolfach.FactorClassPruning

@[expose] public section
/-! Retaining the large classes does not remove any member of such a class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_retained_class_card {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (n κL κS:ℝ):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let small:=fun j:Option (Fin K)=>
      ((fibres j).card:ℝ)<(if j=none then κL*n else κS*n)
    let removed:=Finset.univ.filter (fun w=>small (classify w));
    ∀ j,¬small j→
      (Finset.univ.filter (fun w:{w:W // w∉removed}=>classify w.val=j)).card=(fibres j).card:=by
  intro fibres small removed j hj
  apply Finset.card_bij (fun w _=>w.val)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro w hw
    have hclass:classify w=j:=(Finset.mem_filter.mp hw).2
    have hnot:w∉removed:=by
      intro h
      have hsmall:small (classify w):=(Finset.mem_filter.mp h).2
      rw [hclass] at hsmall
      exact hj hsmall
    exact ⟨⟨w,hnot⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hclass⟩,rfl⟩

/-- The lower density is measured in the actual residual host and actual
retained index set, rather than in the original family. -/
theorem factor_retained_class_actual_density {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (n D κL κS:ℝ)
    (hn:0≤n) (hD:0<D) (hDn:D≤n) (hL:0≤κL) (hS:0≤κS):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w));
    ∀ j,¬small j→2*cutoff j≤
      2*((Finset.univ.filter (fun w:{w:W // w∉removed}=>classify w.val=j)).card:ℝ)/D:=by
  intro fibres cutoff small removed j hj
  have hcard:(Finset.univ.filter (fun w:{w:W // w∉removed}=>classify w.val=j)).card=(fibres j).card:=by
    apply Finset.card_bij (fun w _=>w.val)
    · intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩
    · intro x _ y _ h
      exact Subtype.ext h
    · intro w hw
      have hclass:classify w=j:=(Finset.mem_filter.mp hw).2
      have hnot:w∉removed:=by
        intro h
        have hsmall:small (classify w):=(Finset.mem_filter.mp h).2
        rw [hclass] at hsmall
        exact hj hsmall
      exact ⟨⟨w,hnot⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hclass⟩,rfl⟩
  have hf:cutoff j*n≤(fibres j).card:=le_of_not_gt hj
  have hden:=factor_retained_class_density K classify n D κL κS hn hD hDn hL hS j hf
  rw [hcard]
  exact hden
end Oberwolfach
