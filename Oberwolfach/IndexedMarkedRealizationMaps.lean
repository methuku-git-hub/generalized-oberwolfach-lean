module

public import Oberwolfach.IndexedMarkedHostRealization
public import Oberwolfach.IndexedMarkedAttachment

@[expose] public section

/-! Transport of actual host realisations through displayed occurrence
permutations and equality of the mapped indexed graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V₁ U₁ V U E K A S:Type} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

def IndexedMarkedHostRealization.reindex {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (τ:Equiv.Perm A) (σ:Equiv.Perm S):
    IndexedMarkedHostRealization (G.reindex τ σ) tail head ktail khead H₀ HK π b where
  rows:=R.rows
  hubs:=R.hubs
  rimPresent:=fun a=>R.rimPresent (τ a)
  spokePresent:=fun s=>R.spokePresent (σ s)
  arcSeparated:=fun a=>R.arcSeparated (τ a)
  rimInjective:=R.rimInjective.comp τ.injective
  spokeInjective:=R.spokeInjective.comp σ.injective

def IndexedMarkedHostRealization.ofMapEq
    (G:IndexedMarkedGraph V₀ U₀ A S) {G':IndexedMarkedGraph V₁ U₁ A S}
    (R:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (f:V₀→V) (g:U₀→U) (he:G.map f g=G'.map R.rows R.hubs):
    IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b:=by
  have hs:∀ a,f (G.src a)=R.rows (G'.src a):=fun a=>congrArg (fun D=>D.src a) he
  have hd:∀ a,f (G.dst a)=R.rows (G'.dst a):=fun a=>congrArg (fun D=>D.dst a) he
  have hr:∀ s,f (G.row s)=R.rows (G'.row s):=fun s=>congrArg (fun D=>D.row s) he
  have hh:∀ s,g (G.hub s)=R.hubs (G'.hub s):=fun s=>congrArg (fun D=>D.hub s) he
  have hja:∀ a,G.jr a=G'.jr a:=fun a=>congrArg (fun D=>D.jr a) he
  have hjs:∀ s,G.js s=G'.js s:=fun s=>congrArg (fun D=>D.js s) he
  refine ⟨f,g,?_,?_,?_,?_,?_⟩
  · simpa only [hs,hd,hja] using R.rimPresent
  · simpa only [hr,hh,hjs] using R.spokePresent
  · simpa only [hs,hd] using R.arcSeparated
  · simpa only [hs,hd,hja] using R.rimInjective
  · simpa only [hr,hh] using R.spokeInjective

theorem IndexedMarkedGraph.map_map (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V₁) (g:U₀→U₁) (f':V₁→V) (g':U₁→U):
    (G.map f g).map f' g'=G.map (f'∘f) (g'∘g):=rfl

theorem IndexedMarkedGraph.reindex_map (G:IndexedMarkedGraph V₀ U₀ A S)
    (τ:Equiv.Perm A) (σ:Equiv.Perm S) (f:V₀→V) (g:U₀→U):
    (G.reindex τ σ).map f g=(G.map f g).reindex τ σ:=rfl

end Oberwolfach
