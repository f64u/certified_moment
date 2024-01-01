import «TypedAssembly».Common.TypEnv
import «TypedAssembly».Common.SubstOne
import «TypedAssembly».Common.Rent

inductive Typ    : Ctxt → Kind → Type where
  | var {j}      : Δ ∋⋆ j → Typ Δ j
  | int          : Typ Δ ⋆
  | unit         : Typ Δ ⋆ -- aka, an empty product 
  | arrow        : Typ Δ ⋆ → Typ Δ ⋆ → Typ Δ ⋆
  | prod         : Typ Δ ⋆ → Typ Δ ⋆ → Typ Δ ⋆
  | for_all {j}  : Typ (Δ ,⋆ j) ⋆ → Typ Δ ⋆
  deriving BEq, DecidableEq

namespace Typ
  infixl:90 " ⊢F⋆ " => Typ

  declare_syntax_cat typf
  syntax "!" term:max : typf
  syntax:90 "♯" num : typf
  syntax " int " : typf
  syntax " () " : typf
  syntax:50 typf (" → " <|> " -> ") typf : typf
  syntax:50 typf " × " typf : typf
  syntax:10 "∀. " typf : typf
  syntax " f⋆⟪ " typf " ⟫ " : term

  syntax " ( " typf " ) " : typf
  
  macro_rules 
  | `( f⋆⟪ !$t ⟫) => `($t)
  | `( f⋆⟪ int ⟫ ) => `(Typ.int)
  | `( f⋆⟪ () ⟫ ) => `(Typ.unit)
  | `( f⋆⟪ ♯$n ⟫ ) => `(Typ.var (by get_elem $n))
  | `( f⋆⟪ $t₁ → $t₂ ⟫ ) => `(Typ.arrow f⋆⟪ $t₁ ⟫ f⋆⟪ $t₂ ⟫)
  | `( f⋆⟪ $t₁ × $t₂ ⟫ ) => `(Typ.prod f⋆⟪ $t₁ ⟫ f⋆⟪ $t₂ ⟫)
  | `( f⋆⟪ ∀. $t ⟫) => `(Typ.for_all f⋆⟪ $t ⟫)
  | `( f⋆⟪ ( $t )  ⟫ ) => `(f⋆⟪ $t ⟫)

  example : Ø ,⋆ ⋆ ,⋆ ⋆ ,⋆ ⋆ ⊢F⋆ ⋆ := f⋆⟪ ♯2 ⟫
  def polyidt : Δ ⊢F⋆ ⋆ := f⋆⟪ ∀. ♯0 → ♯0 ⟫

  def repr : Typ Δ k → String
  | .var x => Lookupt.repr x
  | .int => "int"
  | .unit => "()"
  | .arrow t₁ t₂ => s!"({repr t₁} → {repr t₂})"
  | .prod t₁ t₂ => s!"({repr t₁} × {repr t₂})"
  | .for_all t => s!"(∀. {repr t})"
end Typ
open Typ

instance : Repr (Δ ⊢F⋆ k) where
  reprPrec t _ := t.repr

instance : ToString (Δ ⊢F⋆ k) where
  toString := repr
 
/-- renτ takes a Renτ and a typ and applies it to that typ,
    essentially moving it from one typing ctxt to another. -/
 def renτ {Δ₁ Δ₂} : Renτ Δ₁ Δ₂ → ∀ {k}, Δ₁ ⊢F⋆ k → Δ₂ ⊢F⋆ k 
  |  _, _, .int => .int
  |  _, _, .unit => .unit
  | rt, _, .var a => .var (rt a)
  | rt, _, .arrow t₁ t₂ => .arrow (renτ rt t₁) (renτ rt t₂)
  | rt, _, .prod t₁ t₂ => .prod (renτ rt t₁) (renτ rt t₂)
  | rt, _, .for_all t => .for_all (renτ (liftτ rt) t)

/-- weakenτ takes a typ and returns a typ where all 
    free typ variables in that typ have been shifted right by 1 position -/
def weakenτ {Δ j k} : Δ ⊢F⋆ j → Δ ,⋆ k ⊢F⋆ j := renτ .there

theorem renτ_id : ∀ {Δ j} {t : Δ ⊢F⋆ j}, renτ id t = t := by
  intros Δ j t
  induction t <;> simp_all!

  case for_all Δ' j' t' t'_ih =>
    have : (fun {j} => @liftτ Δ' Δ' id j' j) = (fun {j} => @id (Δ' ,⋆ j' ∋⋆ j)) := by
      funext j a
      apply liftτ_id
    rw [this]
    assumption

theorem renτ_comp : ∀ {Δ₁ Δ₂ Δ₃} {rt₁ : Renτ Δ₁ Δ₂} {rt₂ : Renτ Δ₂ Δ₃} {j} {t : Δ₁ ⊢F⋆ j},
                    renτ (rt₂ ∘ rt₁) t = renτ rt₂ (renτ rt₁ t) := by
  intros Δ₁ Δ₂ Δ₃ rt₁ rt₂ j t
  induction t generalizing Δ₂ Δ₃ rt₂ <;> simp_all!

  case for_all Δ' k t' t'_ih =>
    have : (fun {j} =>
      @liftτ Δ' Δ₃
        (fun {j : Kind} => rt₂ ∘ rt₁) k j) = (fun {j} => liftτ rt₂ ∘ liftτ rt₁) := by 
        funext _ t
        apply liftτ_comp

    rw [this]
    exact (@t'_ih _ _ (liftτ rt₁) (liftτ rt₂))

theorem weakenτ_renτ : ∀ {Δ₁ Δ₂} (rt : Renτ Δ₁ Δ₂) {k} (t : Δ₁ ⊢F⋆ k), 
                        weakenτ (renτ rt t) = renτ (liftτ rt (k := k)) (weakenτ t) := by
  intros Δ₁ Δ₂ rt k t 
  simp [weakenτ]
  repeat rw [←renτ_comp]
  congr

/-- A Subsτ Δ₁ Δ₂ is a function that maps typ variables to typs -/
@[reducible]
def Subsτ (Δ₁ Δ₂ : Ctxt) : Type :=
  ∀ {j}, Δ₁ ∋⋆ j → Δ₂ ⊢F⋆ j

/-- liftsτ takes a Subsτ and returns a transformed Subsτ that does the following:
      1. The first typ variable is unaffected (no Subsτ is not applied to it)
      2. All further variables have the Subsτ applied to a shift-down version of them,
         and the but all free typ variables (that were not subsτed) are brought back to their 
         original position.
    This transformation is helpful for substituting under the binders (namely ∀.) -/
def liftsτ {Δ₁ Δ₂} (st :  Subsτ Δ₁ Δ₂) {k} : Subsτ (Δ₁ ,⋆ k) (Δ₂ ,⋆ k)
  | _, .here => .var .here
  | _, .there a => weakenτ (st a)


/-- subsτ takes a Subsτ and a typ and applies it to the free variables in it -/
def subsτ {Δ₁ Δ₂} : Subsτ Δ₁ Δ₂ → ∀ {j}, Δ₁ ⊢F⋆ j → Δ₂ ⊢F⋆ j 
  |  _, _, .int => .int
  |  _, _, .unit => .unit
  | st, _, .var a => st a
  | st, _, .arrow t₁ t₂ => .arrow (subsτ st t₁) (subsτ st t₂)
  | st, _, .prod t₁ t₂ => .prod (subsτ st t₁) (subsτ st t₂)
  | st, _, .for_all t => .for_all (subsτ (liftsτ st) t)

/-- extendτ is a Subsτ that, given a Subsτ and a typ, replaces the first free typ var with
    that typ and applies the the given substitution to a shifted-down version of all further typ vars -/
def extendτ {Δ₁ Δ₂} : Subsτ Δ₁ Δ₂ → ∀ {k}, (Δ₂ ⊢F⋆ k) → Subsτ (Δ₁ ,⋆ k) Δ₂
  |  _, _, t, _, .here => t
  | st, _, _, _, .there a => st a

@[simp]
def subsτ_one {Δ j k} (t₁ : Δ ,⋆ k ⊢F⋆ j) (t₂ : Δ ⊢F⋆ k) : Δ ⊢F⋆ j :=
  (subsτ (extendτ .var t₂) t₁)

instance : SubsτOne Typ where
  subsτ_one := subsτ_one

example : f⋆⟪ ♯0 → ♯0 ⟫[.int]⋆ = (f⋆⟪ int → int ⟫ : Ø ⊢F⋆ ⋆) := rfl

theorem liftsτ_liftτ : ∀ {Δ₁ Δ₂ Δ₃} (rt : Renτ Δ₁ Δ₂) (st : Subsτ Δ₂ Δ₃)
                         {j k} (x : Δ₁ ,⋆ k ∋⋆ j), 
                         liftsτ (st ∘ rt) x = liftsτ st (liftτ rt x) := by
  intros Δ₁ Δ₂ Δ₃ rt st j k x
  cases x <;> rfl

theorem subsτ_renτ : ∀ {Δ₁ Δ₂ Δ₃} (rt : Renτ Δ₁ Δ₂) (st : Subsτ Δ₂ Δ₃)
                        {j} (t : Δ₁ ⊢F⋆ j),
                        subsτ (st ∘ rt) t = subsτ st (renτ rt t) := by
  intros Δ₁ Δ₂ Δ₃ rt st j t
  induction t generalizing Δ₂ Δ₃ with simp_all!
  | for_all t' t'_ih =>
    rw [←t'_ih]
    congr
    funext _ x
    cases x <;> rfl

theorem renτ_liftτ_liftsτ : ∀ {Δ₁ Δ₂ Δ₃} (st : Subsτ Δ₁ Δ₂) (rt : Renτ Δ₂ Δ₃)
                              {j k} (x : Δ₁ ,⋆ k ∋⋆ j),
                              liftsτ (renτ rt ∘ st) x = renτ (liftτ rt) (liftsτ st x) := by
  intros Δ₁ Δ₂ Δ₃ st rt j k x
  cases x
  case here => rfl
  case there x' => 
    simp [liftsτ, weakenτ]
    repeat rw [←renτ_comp]
    congr

theorem renτ_subsτ : ∀ {Δ₁ Δ₂ Δ₃} (st : Subsτ Δ₁ Δ₂) (rt : Renτ Δ₂ Δ₃)
                       {j} (t : Δ₁ ⊢F⋆ j),
                       subsτ (renτ rt ∘ st) t = renτ rt (subsτ st t) := by
  intros Δ₁ Δ₂ Δ₃ st rt j t
  induction t generalizing Δ₂ Δ₃ with simp_all!
  | for_all t' t'_ih =>
    rw [←t'_ih]
    congr
    funext _ x
    cases x
    case here => rfl
    case there x' =>
      simp [liftsτ]
      apply weakenτ_renτ

theorem liftsτ_id : ∀ {Δ j k} (x : Δ ,⋆ j ∋⋆ k), liftsτ .var x = .var x := by 
  intros Δ j k x
  cases x <;> rfl

theorem liftsτ_comp : ∀ {Δ₁ Δ₂ Δ₃} (st₁ : Subsτ Δ₁ Δ₂) (st₂ : Subsτ Δ₂ Δ₃)
                        {j k} (x : Δ₁ ,⋆ k ∋⋆ j),
                        liftsτ (subsτ st₂ ∘ st₁) x = subsτ (liftsτ st₂) (liftsτ st₁ x) := by
  intros Δ₁ Δ₂ Δ₃ st₁ st₂ j k x
  cases x
  case here => rfl
  case there x' => 
    simp [liftsτ, weakenτ]
    rw [←subsτ_renτ, ←renτ_subsτ]
    congr

theorem subsτ_id : ∀ {Δ j} (t : Δ ⊢F⋆ j), subsτ .var t = t := by
  intros Δ j t 
  induction t <;> simp_all!

  case for_all Δ' k t' t'_ih =>
    have : (fun {j} => @liftsτ Δ' Δ' .var k j) = (fun {j} => @Typ.var (Δ' ,⋆ k) j) := by
          funext _ t
          cases t <;> rfl
    rw [this]
    assumption

theorem subsτ_var : ∀ {Δ₁ Δ₂} {st : Subsτ Δ₁ Δ₂} {j} (x : Δ₁ ∋⋆ j), 
                subsτ st (.var x) = st x := by intros; rfl

theorem subsτ_comp : ∀ {Δ₁ Δ₂ Δ₃} {st₁ : Subsτ Δ₁ Δ₂} {st₂ : Subsτ Δ₂ Δ₃} {j} (t : Δ₁ ⊢F⋆ j),
               subsτ (subsτ st₂ ∘ st₁) t = subsτ st₂ (subsτ st₁ t) := by
  intros Δ₁ Δ₂ Δ₃ st₁ st₂ j t
  induction t generalizing Δ₂ Δ₃ <;> simp_all!
   
  case for_all Δ' j' t' t'_ih =>
    have : (fun {j} => @liftsτ Δ' Δ₃ (fun {j} => (subsτ fun {j} => st₂) ∘ st₁) j' j) = (fun {j} => subsτ (liftsτ st₂) ∘ liftsτ st₁) := by 
      funext _ x
      apply liftsτ_comp
     
    rw [this]
    simp_all!

theorem renτ_subsτ_one : ∀ {Δ₁ Δ₂ j k} (rt : Renτ Δ₁ Δ₂) (t₁ : Δ₁ ,⋆ k ⊢F⋆ j) (t₂ : Δ₁ ⊢F⋆ k), renτ rt (t₁[t₂]⋆) = (renτ (liftτ rt) t₁)[renτ rt t₂]⋆ := by
  intros Δ₁ Δ₂ j k rt t₁ t₂
  simp [SubsτOne.subsτ_one]
  rw [←subsτ_renτ, ←renτ_subsτ]
  congr
  funext _ x
  cases x <;> rfl

theorem subsτ_subsτ_one : ∀ {Δ₁ Δ₂ k} (st : Subsτ Δ₁ Δ₂) (t₁ : Δ₁ ⊢F⋆ k) (t₂ : Δ₁ ,⋆ k ⊢F⋆ ⋆),
                          subsτ st (t₂[t₁]⋆) = (subsτ (liftsτ st) t₂)[subsτ st t₁]⋆ := by
  intros Δ₁ Δ₂ k st t₁ t₂
  simp [SubsτOne.subsτ_one]
  repeat rw [←subsτ_comp]
  congr
  funext j x
  cases x 
  · rfl
  · rename_i x'
    simp [extendτ, liftsτ, weakenτ, subsτ]
    rw [←subsτ_renτ]
    have : (fun {j} => extendτ (fun {j} => .var) (subsτ (fun {j} => st) t₁) ∘ Lookupt.there) = fun {j} => @Typ.var Δ₂ j := by
      funext _ x
      cases x <;> rfl
    rw [this, subsτ_id]
