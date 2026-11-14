module

public import Oberwolfach.MarkedTransformerBetweenRootsPaths

@[expose] public section

/-! Actual shared paths for a marked spoke-edge or vertex-wheel pair.
Both attachments see the two old roots. An internal marked head, if present,
has marked spokes at both hubs; all other free vertices have ordinary spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

 theorem marked_transformer_common_path (F:SimpleGraph V)
    (R₀ RK:V→V→Prop) (H₀ HK:V→U→Prop) (v v':V) (u u':U) (j:Bool)
    (W Z:Finset V) (hv:v∈Z) (hv':v'∈Z) (l:ℕ) (hl:2≤l)
    (d c:ℝ) (hd:0≤d) (hF:∀ x,(F.degree x:ℝ)≤d)
    (hopen:c≤((Finset.univ.filter (fun a=>R₀ v a∧R₀ v' a∧H₀ a u∧H₀ a u')).card:ℝ))
    (hclose:c≤((Finset.univ.filter (fun a=>(if j then RK a v∧RK a v' else R₀ a v∧R₀ a v')∧H₀ a u∧H₀ a u')).card:ℝ))
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      (if t then RK x a else R₀ x a)∧(if t then HK a u∧HK a u' else H₀ a u∧H₀ a u'))).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>R₀ x a∧R₀ a y∧H₀ a u∧H₀ a u')).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(d+1)<c):
    ∃ p:Fin (l+3)↪V,
      (R₀ v (p 0)∧R₀ v' (p 0))∧
      (if j then RK (p (Fin.last (l+2))) v∧RK (p (Fin.last (l+2))) v'
       else R₀ (p (Fin.last (l+2))) v∧R₀ (p (Fin.last (l+2))) v')∧
      (∀ i:Fin (l+2),if j=false∧i.val=1 then RK (p i.castSucc) (p i.succ)
        else R₀ (p i.castSucc) (p i.succ))∧
      (∀ i,if j=false∧i.val=2 then HK (p i) u∧HK (p i) u'
        else H₀ (p i) u∧H₀ (p i) u')∧
      (∀ i,p i∉W∧p i∉Z∧∀ z∈Z,¬F.Adj (p i) z)∧
      ∀ i k,¬F.Adj (p i) (p k):=by
  exact marked_transformer_between_roots_path F R₀ RK H₀ HK v v' v v' u u' j j
    W Z l hl d c hd hF hopen hclose hstep hjoin hbudget

end Oberwolfach
