module

public import Oberwolfach.MarkedRestrictedSampleSeedBounds
public import Oberwolfach.MarkedInducedSampleStates

@[expose] public section

/-! Transport an induced sample to the actual complementary row and hub types.
The parent tuple weights, error and coefficient bounds are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V VA U UA Γ Color:Type} [Fintype V] [Fintype VA] [Fintype U] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [DecidableEq U] [DecidableEq UA]

theorem marked_complement_seed_transfer
    (f:VA↪oV) (g:UA↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm VA)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (T:Finset V) (Z:Finset U) (hT:∀ x,π x∈T↔x∈T)
    (hfX:Finset.univ.image f=Finset.univ\T) (hgX:Finset.univ.image g=Finset.univ\Z)
    (weight:(Fin (m+1)→V)→ℝ) (η lo hi:ℝ):
    let X:=Finset.univ\T
    let P₀:=spanningRestriction P X
    let H':=fun j v u=>H j v u∧v∉T∧u∉Z
    let E₀:=MarkedSampleArc P₀ π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P₀ π (3*d) (fun e=>σ (Sum.inl e)) true
    let σA:=rawMarkedRestrictPair f g σ
    let EA₀:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let EA₁:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d) (H' false) (H' true)=>weight W.1.val
    let ψA:=fun W:MarkedWheel (fun a:EA₀=>a.val.1) (fun a=>a.val.2)
      (fun a:EA₁=>a.val.1) (fun a=>a.val.2) m ρ (3*d)
      (fun v u=>H false (f v) (g u)) (fun v u=>H true (f v) (g u))=>weight (f∘W.1.val)
    (∀ a:E₀⊕E₁,|markedWheelRimLoad ψ a-1|≤η)→
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η)→
    (∀ W,lo≤ψ W∧ψ W≤hi)→
    (∀ a:EA₀⊕EA₁,|markedWheelRimLoad ψA a-1|≤η)∧
    (∀ j v u,|markedSpokeResidual ψA j v u|≤η)∧
    (∀ W,lo≤ψA W∧ψA W≤hi):=by
  intro X P₀ H' E₀ E₁ σA EA₀ EA₁ ψ ψA hR hS hψ
  have hfT (x:VA):f x∉T:=by
    have hx:f x∈Finset.univ.image f:=Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    rw [hfX] at hx
    exact (Finset.mem_sdiff.mp hx).2
  have hgZ (u:UA):g u∉Z:=by
    have hu:g u∈Finset.univ.image g:=Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
    rw [hgX] at hu
    exact (Finset.mem_sdiff.mp hu).2
  have hX:∀ x,π x∈X↔x∈X:=by intro x;simp only [X,Finset.mem_sdiff,Finset.mem_univ,true_and,hT]
  have hA (j:Bool) (a:MarkedSampleArc P₀ π (3*d) (fun e=>σ (Sum.inl e)) j):
      a.val.1∈Finset.univ.image f∧a.val.2∈Finset.univ.image f:=by
    rw [hfX]
    exact markedSampleArc_spanningRestriction_support P π (3*d) X hX _ j a
  have hSp (v:V) (u:U) (he:H' false v u∨H' true v u):
      v∈Finset.univ.image f∧u∈Finset.univ.image g:=by
    rw [hfX,hgX]
    have hh:v∉T∧u∉Z:=he.elim And.right And.right
    simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hh
  have hh:=marked_restricted_sample_seed_bounds f g π ρ hf P₀ d m σ H' hA hSp weight η lo hi hR hS hψ
  have hP:P₀.comap f=P.comap f:=by
    ext x y
    change (spanningRestriction P X).Adj (f x) (f y)↔P.Adj (f x) (f y)
    simp only [spanningRestriction_adj,X,Finset.mem_sdiff,Finset.mem_univ,true_and,hfT,not_false_eq_true,and_true]
  have hH (j:Bool):(fun v u=>H' j (f v) (g u))=(fun v u=>H j (f v) (g u)):=by
    funext v u
    exact propext (by dsimp [H'];simp only [hfT,hgZ,not_false_eq_true,and_true])
  rw [hP, hH false, hH true] at hh
  exact hh

end Oberwolfach
