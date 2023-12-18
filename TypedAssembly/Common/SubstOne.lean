import «TypedAssembly».Common.TypEnv

class SubsτOne (Typ : Ctxt → Kind → Type) where
  subsτ_one {Δ j k} : (t₁ : Typ (Δ ,⋆ k) j) → (t₂ : Typ Δ k) → Typ Δ j 

macro b:term:80 "[" a:term:80 "]⋆" : term => `(SubsτOne.subsτ_one $b $a)

