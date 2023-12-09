import «TypedAssembly».SystemF.Kind
import «TypedAssembly».SystemF.TypEnv


inductive Typ   : Ctxt → Kind → Type where
  | var {j}     : Δ ∋⋆ j → Typ Δ j
  | int         : Typ Δ ⋆
  | arrow       : Typ Δ ⋆ → Typ Δ ⋆ → Typ Δ ⋆
  | prod        : Typ Δ ⋆ → Typ Δ ⋆ → Typ Δ ⋆
  | for_all {j} : Typ (Δ ,⋆ j) ⋆ → Typ Δ ⋆
  deriving BEq, DecidableEq, Repr

namespace Typ
  infixl:90 " ⊢⋆ " => Typ
  syntax "♯" term : term
  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookupt.here)
  | n+1 => `(tactic| apply Lookupt.there; get_elem $(Lean.quote n))

  declare_syntax_cat typ
  syntax "!" term:max : typ
  syntax:90 "♯" num : typ
  syntax " int " : typ
  syntax:50 typ (" → " <|> " -> ") typ : typ
  syntax:50 typ " × " typ : typ
  syntax:10 "∀. " typ : typ
  syntax " ⋆⟪ " typ " ⟫ " : term

  syntax " ( " typ " ) " : typ
  
  macro_rules 
  | `( ⋆⟪ !$t ⟫) => `($t)
  | `( ⋆⟪ int ⟫ ) => `(Typ.int)
  | `( ⋆⟪ ♯$n ⟫ ) => `(Typ.var (by get_elem $n))
  | `( ⋆⟪ $t₁ → $t₂ ⟫ ) => `(Typ.arrow ⋆⟪ $t₁ ⟫ ⋆⟪ $t₂ ⟫)
  | `( ⋆⟪ $t₁ × $t₂ ⟫ ) => `(Typ.prod ⋆⟪ $t₁ ⟫ ⋆⟪ $t₂ ⟫)
  | `( ⋆⟪ ∀. $t ⟫) => `(Typ.for_all ⋆⟪ $t ⟫)
  | `( ⋆⟪ ( $t )  ⟫ ) => `(⋆⟪ $t ⟫)

  example : Ø ,⋆ ⋆ ,⋆ ⋆ ,⋆ ⋆ ⊢⋆ ⋆ := ⋆⟪ ♯2 ⟫
  def polyidt : Δ ⊢⋆ ⋆ := ⋆⟪ ∀. ♯0 → ♯0 ⟫

end Typ
open Typ

/-- A Ren⋆ Δ₁ Δ₂ is a funciton that takes a typ variable and moves it
    from the first typing context to the second --/
@[reducible]
def Rent (Δ₁ Δ₂ : Ctxt) : Type :=
  ∀ {j}, (Δ₁ ∋⋆ j) → (Δ₂ ∋⋆ j)

/-- lift⋆ takes a Ren⋆ and returns a different Ren⋆ that does not alter the first variable
    but all other variables are further shifted right and have the Ren⋆ applied to the shifted-left version of them.
    This transformation is helpful for renaming under the binders (namely ∀.) -/
def liftt {Δ₁ Δ₂} : Rent Δ₁ Δ₂ → ∀ {k}, Rent (Δ₁ ,⋆ k) (Δ₂ ,⋆ k)
  |  _, _, _, .here => .here
  | rt, _, _, .there a => .there (rt a)
 
/-- ren⋆ takes a Ren⋆ and a typ and applies it to that typ, moving it to the
    new context -/
 def rent {Δ₁ Δ₂} : Rent Δ₁ Δ₂ → ∀ {k}, Δ₁ ⊢⋆ k → Δ₂ ⊢⋆ k 
  |  _, _, .int => .int
  | rt, _, .var a => .var (rt a)
  | rt, _, .arrow t₁ t₂ => .arrow (rent rt t₁) (rent rt t₂)
  | rt, _, .prod t₁ t₂ => .prod (rent rt t₁) (rent rt t₂)
  | rt, _, .for_all t => .for_all (rent (liftt rt) t)

/-- weaken⋆ takes a typ and returns a typ where all 
    free typ variables in that typ have been shifted right by 1 position -/
def weakent {Δ j k} : Δ ⊢⋆ j → Δ ,⋆ k ⊢⋆ j := rent .there

theorem liftt_id : ∀ {Δ j k} {a : Δ ,⋆ k ∋⋆ j}, liftt id a = a := by
  intros Δ j k a
  cases a <;> simp [liftt]

theorem liftt_comp : ∀ {Δ₁ Δ₂ Δ₃} {rt₁ : Rent Δ₁ Δ₂} {rt₂ : Rent Δ₂ Δ₃} {j k} {a : Δ₁ ,⋆ k ∋⋆ j},
                     liftt (rt₂ ∘ rt₁) a = liftt rt₂ (liftt rt₁ a) := by
  intros Δ₁ Δ₂ Δ₃ rt₁ rt₂ j k a
  cases a <;> simp [liftt]

theorem rent_id : ∀ {Δ j} {t : Δ ⊢⋆ j}, rent id t = t := by
  intros Δ j t
  induction t <;> try rfl

  case arrow Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp [rent]
    constructor <;> assumption

  case prod Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp [rent]
    constructor <;> assumption

  case for_all Δ' j' t' t'_ih =>
    simp [rent]
    have : (fun {j} => @liftt Δ' Δ' id j' j) = (fun {j} => @id (Δ' ,⋆ j' ∋⋆ j)) := by
      funext j a
      apply liftt_id
    rw [this]
    assumption

theorem rent_comp : ∀ {Δ₁ Δ₂ Δ₃} {rt₁ : Rent Δ₁ Δ₂} {rt₂ : Rent Δ₂ Δ₃} {j} {t : Δ₁ ⊢⋆ j},
                    rent (rt₂ ∘ rt₁) t = rent rt₂ (rent rt₁ t) := by
  intros Δ₁ Δ₂ Δ₃ rt₁ rt₂ j t
  induction t generalizing Δ₂ Δ₃ rt₂ <;> try rfl

  case arrow Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp [rent]
    constructor <;> simp_all! <;> assumption

  case prod Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp [rent]
    constructor <;> simp_all! <;> assumption

  case for_all Δ' k t' t'_ih =>
    simp [rent]
    
    have : (fun {j} =>
      @liftt Δ' Δ₃
        (fun {j : Kind} => rt₂ ∘ rt₁) k j) = (fun {j} => liftt rt₂ ∘ liftt rt₁) := by 
        funext _ t
        apply liftt_comp

    rw [this]
    exact (@t'_ih _ _ (liftt rt₁) (liftt rt₂))

theorem weakent_rent : ∀ {Δ₁ Δ₂} (rt : Rent Δ₁ Δ₂) {k} (t : Δ₁ ⊢⋆ k), 
                        weakent (rent rt t) = rent (liftt rt (k := k)) (weakent t) := by
  intros Δ₁ Δ₂ rt k t 

  induction t generalizing Δ₂ <;> try rfl

  case arrow t₁ t₂ t₁_ih t₂_ih =>
    simp [weakent, rent]
    constructor
    · apply t₁_ih
    · apply t₂_ih

  case prod t₁ t₂ t₁_ih t₂_ih =>
    simp [weakent, rent]
    constructor
    · apply t₁_ih
    · apply t₂_ih
  
  case for_all =>
    simp [weakent, rent] at *
    rw [←rent_comp] at *
    rw [←rent_comp] at *
    congr
    funext j'' x
    cases x <;> rfl

/-- A Subs⋆ Δ₁ Δ₂ is a function that maps typ variables to typs -/
@[reducible]
def Subst (Δ₁ Δ₂ : Ctxt) : Type :=
  ∀ {j}, Δ₁ ∋⋆ j → Δ₂ ⊢⋆ j

/-- lifts⋆ takes a Subs⋆ and returns a transformed Subs⋆ that does the following:
      1. The first typ variable is unaffected (the original Subs⋆ is not applied to it)
      2. All further variables have the Subs⋆ applied to a shift-down version of them,
         and the but all free typ variables (that were not subs⋆ed) are brought back to their 
         original position.
    This transformation is helpful for substituting under the binders (namely ∀.) -/
def liftst {Δ₁ Δ₂} : Subst Δ₁ Δ₂ → ∀ {k}, Subst (Δ₁ ,⋆ k) (Δ₂ ,⋆ k)
  |  _, _, _, .here => .var .here
  | st, _, _, .there a => weakent (st a)

/-- subs⋆ takes a Subs⋆ and a typ and applies it to the free variables in it -/
def subst {Δ₁ Δ₂} : Subst Δ₁ Δ₂ → ∀ {j}, Δ₁ ⊢⋆ j → Δ₂ ⊢⋆ j 
  |  _, _, .int => .int
  | st, _, .var a => st a
  | st, _, .arrow t₁ t₂ => .arrow (subst st t₁) (subst st t₂)
  | st, _, .prod t₁ t₂ => .prod (subst st t₁) (subst st t₂)
  | st, _, .for_all t => .for_all (subst (liftst st) t)

/-- extend⋆ is a Subs⋆ that, given a Subs⋆ and a typ, replaces the first free typ var with
    that typ and applies the the given substitution to a shifted-down version of all further typ vars -/
def extendt {Δ₁ Δ₂} : Subst Δ₁ Δ₂ → ∀ {k}, (Δ₂ ⊢⋆ k) → Subst (Δ₁ ,⋆ k) Δ₂
  |  _, _, t, _, .here => t
  | st, _, _, _, .there a => st a

macro b:term:80 "[" a:term:80 "]⋆" : term => `(subst (extendt .var $a) $b)

example : ⋆⟪ ♯0 → ♯0 ⟫[.int]⋆ = (⋆⟪ int → int ⟫ : Typ Ø ⋆) := rfl

theorem subst_id : ∀ {Δ j} (t : Δ ⊢⋆ j), subst .var t = t := by
  intros Δ j t 
  induction t <;> 
    try rfl 

  case arrow =>
    simp_all!

  case prod =>
    simp_all!

  case for_all Δ' k t' t'_ih =>
    simp_all!
    have : (fun {j} => @liftst Δ' Δ' Typ.var k j) = (fun {j} => @Typ.var (Δ' ,⋆ k) j) := by
          funext _ t
          cases t <;> rfl
    rw [this]
    assumption

theorem subst_var : ∀ {Δ₁ Δ₂} {st : Subst Δ₁ Δ₂} {j} (x : Δ₁ ∋⋆ j), 
                subst st (.var x) = st x := by intros; rfl

theorem weakent_subst : ∀ {Δ₁ Δ₂} (st : Subst Δ₁ Δ₂) {k} (t : Δ₁ ⊢⋆ k),
                        weakent (subst st t) = subst (liftst st (k := k)) (weakent t) := by 
  intros Δ₁ Δ₂ st k t 

  induction t generalizing Δ₂ <;> try rfl

  case arrow Δ' t₁ t₂ t₁_ih t₂_ih => 
    simp [weakent, rent, subst]
    constructor
    · apply t₁_ih
    · apply t₂_ih

  case prod Δ' t₁ t₂ t₁_ih t₂_ih => 
    simp [weakent, rent, subst]
    constructor
    · apply t₁_ih
    · apply t₂_ih

  case for_all Δ' j' t' t'_ih =>
    simp [weakent, rent, subst] at *
    generalize hs : (subst (fun {j} => liftst fun {j} => st) t') = ts
    admit
    /- cases ts <;>
      cases ht' : t' <;> rw [ht'] at hs <;> simp [subst] at hs <;> try contradiction
    · simp [subst, rent] at *
      rename_i x x'
      cases x'
      · simp [liftst] at hs
        rw [←hs]
        rfl
      · simp [liftst, weakent] at hs 
        rename_i x''
        cases hx : st x'' <;>
          rw [hx] at hs <;> simp [rent] at hs <;> try contradiction
        rw [←hs]
        simp [liftt, liftst, weakent]
        rw [hx]
        rfl
    · simp [liftst] at hs 
      rename_i x
      cases x <;> try contradiction
      simp at hs
      simp [weakent] at hs
      rename_i x''
      cases hx : st x'' <;>
          rw [hx] at hs <;> simp [rent] at hs <;> try contradiction
      simp [subst, rent, liftt, liftst]
      rw [hx]
      rfl
    · rfl
    ·  -/

      

      
      
      


      
      
    /- · simp_all!
      simp [weakent, rent] -/

theorem subst_comp : ∀ {Δ₁ Δ₂ Δ₃} {st₁ : Subst Δ₁ Δ₂} {st₂ : Subst Δ₂ Δ₃} {j} (t : Δ₁ ⊢⋆ j),
               subst (subst st₂ ∘ st₁) t = subst st₂ (subst st₁ t) := by
  intros Δ₁ Δ₂ Δ₃ st₁ st₂ j t
  induction t generalizing Δ₂ Δ₃ <;> try rfl 

  case arrow Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp [subst]
    constructor 
    · apply t₁_ih
    · apply t₂_ih

  case prod Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp [subst]
    constructor 
    · apply t₁_ih
    · apply t₂_ih
   
  case for_all Δ' j' t' t'_ih =>
    simp [subst]
    /- set_option pp.all true in
    rfl -/
    have : (fun {j} => @liftst Δ' Δ₃ (fun {j} => (subst fun {j} => st₂) ∘ st₁) j' j) = (fun {j} => subst (liftst st₂) ∘ liftst st₁) := by 
      funext _ x
      cases x
      · simp_all!
      · simp_all!
        apply weakent_subst
      
    rw [this]
    simp_all!

