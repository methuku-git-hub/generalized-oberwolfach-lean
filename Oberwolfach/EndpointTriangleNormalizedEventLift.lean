module

public import Oberwolfach.EndpointTriangleNormalizedFactorFamily
public import Oberwolfach.EndpointTriangleInducedAvoidingFactorLift

@[expose] public section
/-! An endpoint-factor event on the actual inner physical domain lifts to
the original physical graph and retains the same sampling coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J E:Type} [Fintype V] [Fintype W] [Fintype J] [Fintype E]
  [DecidableEq V] [DecidableEq W] [DecidableEq J] [DecidableEq E]

theorem endpoint_triangle_normalized_event_lift
    (e:W↪V) (Q F:SimpleGraph V) (S T:J→Finset V) (g:∀j,V↪E)
    (hS:∀j v,v∈S j→∃w,e w=v) (hT:∀j v,v∈T j→∃w,e w=v)
    (p ζ:ℝ) (σ:E→Bool)
    (hgood:EndpointTriangleNormalizedFactorEvent (Q.comap e) (F.comap e)
      (fun j=>embeddingPullFinset e (S j)) (fun j=>embeddingPullFinset e (T j))
      (fun j=>e.trans (g j)) p ζ σ):
    EndpointTriangleNormalizedFactorEvent Q F S T g p ζ σ :=by
  intro j Y hY hratio hchange K hK
  let Yl:=embeddingPullFinset e Y
  let Sl:=embeddingPullFinset e (S j)
  let Tl:=embeddingPullFinset e (T j)
  let B:Finset V:=(S j∪T j)∩bernoulliVertexSet (fun v=>σ (g j v))
  let Bl:Finset W:=(Sl∪Tl)∩bernoulliVertexSet (fun w=>σ (g j (e w)))
  have hYr:∀v∈Y,∃w,e w=v:=by
    intro v hv
    exact (Finset.mem_union.mp (hY hv)).elim (hS j v) (hT j v)
  have hBr:∀v∈B,∃w,e w=v:=by
    intro v hv
    have hv':v∈S j∪T j:=(Finset.mem_inter.mp hv).1
    exact (Finset.mem_union.mp hv').elim (hS j v) (hT j v)
  have hYl:Yl⊆Sl∪Tl:=by
    intro w hw
    have hh:=hY ((embeddingPullFinset_mem e Y w).mp hw)
    simpa only [Sl,Tl,Finset.mem_union,embeddingPullFinset_mem] using hh
  have hIntS:Yl∩Sl=embeddingPullFinset e (Y∩S j):=by ext w;simp [Yl,Sl]
  have hIntT:Yl∩Tl=embeddingPullFinset e (Y∩T j):=by ext w;simp [Yl,Tl]
  have hSr:∀v∈Y∩S j,∃w,e w=v:=by intro v hv;exact hS j v (Finset.mem_inter.mp hv).2
  have hTr:∀v∈Y∩T j,∃w,e w=v:=by intro v hv;exact hT j v (Finset.mem_inter.mp hv).2
  have hratio':(Yl∩Sl).card=2*(Yl∩Tl).card:=by
    rw [hIntS,hIntT,embeddingPullFinset_card e (Y∩S j) hSr,embeddingPullFinset_card e (Y∩T j) hTr]
    exact hratio
  have hBl:Bl=embeddingPullFinset e B:=by
    ext w
    simp [Bl,B,Sl,Tl,bernoulliVertexSet]
  have hdiff1:Bl\Yl=embeddingPullFinset e (B\Y):=by ext w;simp [hBl,Yl]
  have hdiff2:Yl\Bl=embeddingPullFinset e (Y\B):=by ext w;simp [hBl,Yl]
  have hdiff1r:∀v∈B\Y,∃w,e w=v:=by intro v hv;exact hBr v (Finset.mem_sdiff.mp hv).1
  have hdiff2r:∀v∈Y\B,∃w,e w=v:=by intro v hv;exact hYr v (Finset.mem_sdiff.mp hv).1
  have hTc:Tl.card=(T j).card:=embeddingPullFinset_card e (T j) (hT j)
  have hchange':((Bl\Yl).card+(Yl\Bl).card:ℝ)≤ζ*(p*Tl.card):=by
    rw [hdiff1,hdiff2,embeddingPullFinset_card e (B\Y) hdiff1r,
      embeddingPullFinset_card e (Y\B) hdiff2r,hTc]
    simpa only [B,Nat.cast_add] using hchange
  have hK':∀w,((K.comap e).degree w:ℝ)≤ζ*(p*Tl.card):=by
    intro w
    rw [hTc]
    have hh:((K.comap e).degree w:ℝ)≤K.degree (e w):=by exact_mod_cast embedding_comap_degree_le e K w
    exact hh.trans (hK (e w))
  have hh:=hgood j Yl hYl hratio' (by simpa only [Bl,Sl,Tl,Function.Embedding.trans_apply,Nat.cast_add] using hchange') (K.comap e) hK'
  obtain ⟨M,⟨hM,hcover⟩,havoid⟩:=hh
  obtain ⟨M',hM',hcover',havoid'⟩:=endpoint_triangle_induced_avoiding_factor_lift e Q F K (S j) (T j) Y (hS j) (hT j) hY M hM hcover havoid
  exact ⟨M',⟨hM',hcover'⟩,havoid'⟩
end Oberwolfach
