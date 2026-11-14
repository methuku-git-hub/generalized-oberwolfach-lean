module

public import Oberwolfach.MarkedProtectedActiveSpokeData

@[expose] public section

/-! Original fixed-domain neighbourhood profiles give the active spoke
intersection data. The close-pair exceptional set remains explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A U B Γ Color:Type} [Fintype V] [Fintype A] [Fintype U] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_active_spoke_data_from_scale
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d h:ℕ) (hh:3≤h)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (c:Γ) (j:Color)
    (hp:0≤p∧p≤1) (hk:0≤k∧k≤1) (hq:∀ u,0≤q u c∧q u c≤1) (hs:∀ u,0≤s u j∧s u j≤1)
    (kappa omega p₀ delta:ℝ) (hκ:0≤kappa) (ho:0<omega)
    (hA:(Fintype.card V:ℝ)/2≤Fintype.card A) (hB:omega*Fintype.card V/2≤Fintype.card B)
    (hRsize:((Finset.univ\Finset.univ.image f).card:ℝ)≤kappa*Fintype.card V)
    (hUsize:((Finset.univ\Finset.univ.image g).card:ℝ)≤kappa*Fintype.card V)
    (hrowBudget:2*(2+2*(h:ℝ))*kappa≤delta)
    (hcolBudget:2*(2+(h:ℝ))*kappa≤delta*p₀^2*omega)
    (density:Bool→ℝ) (hp₀:0<p₀) (hden0:∀ b,p₀≤density b) (hden1:∀ b,density b≤1)
    (hden:∀ b u,(if b then q u c else s u j)=density b)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h Finset.univ p k q s c j (kappa*Fintype.card V) σ H)
    (hi:MarkedIndicesWithSpokes π d h Finset.univ q s c j (kappa*Fintype.card V) σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card V)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card V):
    ∀ mark,SparseIntersectionData (fun x u=>markedDeletePhysicalSpokes H DS mark (f x) (g u))
      (fun _=>density mark) (fun _=>1/density mark) (max 1 (1/p₀)) delta (6*d+1):=by
  have hδ:0≤delta:=le_trans (by positivity) hrowBudget
  have hn:0≤(Fintype.card V:ℝ):=Nat.cast_nonneg _
  have hrowN:=mul_le_mul_of_nonneg_right hrowBudget hn
  have hrowA:=mul_le_mul_of_nonneg_left hA hδ
  have hcolN:=mul_le_mul_of_nonneg_right hcolBudget hn
  have hcolA:=mul_le_mul_of_nonneg_left hB (show 0≤delta*p₀^2 by positivity)
  apply marked_protected_active_spoke_data f g π ρ hf P d h hh p k q s c j hp hk hq hs
    (kappa*Fintype.card V) (kappa*Fintype.card V)
    (kappa*Fintype.card V) (kappa*Fintype.card V) (kappa*Fintype.card V) p₀ delta
    (by positivity) (by positivity) (by positivity) density hp₀ hden0 hden1 hδ hden
    _ _ σ H hr hi DR DS hrim hrow hcol
  · nlinarith only [hRsize,hrowN,hrowA]
  · nlinarith only [hUsize,hcolN,hcolA]

end Oberwolfach
