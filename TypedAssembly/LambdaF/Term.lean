import «TypedAssembly».LambdaF.Typ
import «TypedAssembly».Common.Prim
import «TypedAssembly».LambdaF.TermEnv

inductive Term : {Δ : Ctxt} → Ctx Δ → Δ ⊢F⋆ ⋆ → Type where
  | int  {Γ : Ctx Δ} : Int → Term Γ .int
  | unit {Γ : Ctx Δ} : Term Γ .unit
  | var  {Γ : Ctx Δ} {t : Δ ⊢F⋆ ⋆} : Γ ∋ t → Term Γ t

  | fix  {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : Term (Γ ,, f⋆⟪ !t₁ → !t₂ ⟫ ,, t₁ ) t₂ → Term Γ f⋆⟪ !t₁ → !t₂ ⟫
  | app  {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : Term Γ f⋆⟪ !t₁ → !t₂ ⟫ → Term Γ t₁ → Term Γ t₂

  | Λ    {Γ : Ctx Δ} {k} {t : Δ ,⋆ k ⊢F⋆ ⋆} : Term (Γ ,,⋆ k) t → Term Γ f⋆⟪ ∀. !t ⟫
  | sub  {Γ : Ctx Δ} {k} {t₁ : Δ ,⋆ k ⊢F⋆ ⋆} : Term Γ f⋆⟪ ∀. !t₁ ⟫ → (t₂ : Δ ⊢F⋆ k) → Term Γ (t₁[t₂]⋆)

  | prim {Γ : Ctx Δ} : Term Γ .int → Prim → Term Γ .int → Term Γ .int
  | pair {Γ : Ctx Δ} : Term Γ t₁ → Term Γ t₂ → Term Γ f⋆⟪ !t₁ × !t₂ ⟫
  | fst  {Γ : Ctx Δ} : Term Γ f⋆⟪ !t₁ × !t₂ ⟫ → Term Γ t₁
  | snd  {Γ : Ctx Δ} : Term Γ f⋆⟪ !t₁ × !t₂ ⟫ → Term Γ t₂
  | if0  {Γ : Ctx Δ} {t : Δ ⊢F⋆ ⋆} : Term Γ .int → Term Γ t → Term Γ t → Term Γ t

namespace Term 
  notation:50 Γ " ⊢F " t => Term Γ t

  syntax "get_elem'" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem' $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.here)
  | n+1 => `(tactic| apply Lookup.there; get_elem' $(Lean.quote n))

  macro "# " n:term:90 : term => `(Term.var (by get_elem' $n))

  example : (∅ ,, f⋆⟪ int → int ⟫ ,, .int) ⊢F f⋆⟪ int ⟫ := #0
  example : (∅ ,, f⋆⟪ int → int ⟫ ,, .int) ⊢F f⋆⟪ int → int ⟫ := #1
  
  declare_syntax_cat trm
  syntax "!" term:max : trm
  syntax num : trm 
  syntax " () " : trm 
  syntax "#" num : trm
  syntax " λ. " trm : trm
  syntax trm trm : trm
  syntax " Λ. " trm : trm
  syntax trm "[ " typf " ] " : trm
  syntax:20 trm:20 " + " trm:21 : trm
  syntax:20 trm:20 " - " trm:21 : trm
  syntax:30 trm:30 " * " trm:31 : trm
  syntax " ( " trm ", " trm " ) " : trm
  syntax "π₁" trm : trm
  syntax "π₂" trm : trm
  syntax "if0 " trm " then " trm " else " trm " end " : trm
  syntax "if0 " " ( " trm " , " trm " , " trm " ) " : trm

  syntax " ( " trm " ) " : trm
  syntax " f⟪ " trm " ⟫" : term

  macro_rules
    | `( f⟪ !$t ⟫) => `($t)
    | `( f⟪ $i:num ⟫ ) => `(Term.int $i)
    | `( f⟪ () ⟫ ) => `(Term.unit)
    | `( f⟪ #$i:num ⟫ ) => `(#$i)
    | `( f⟪ λ. $e ⟫ ) => `(Term.fix f⟪ $e ⟫)
    | `( f⟪ $e₁ $e₂  ⟫) => `(Term.app f⟪ $e₁ ⟫ f⟪ $e₂ ⟫ )
    | `( f⟪ Λ. $e ⟫ ) => `(Term.Λ f⟪ $e ⟫ )
    | `( f⟪ $e[$t] ⟫ ) => `(Term.sub f⟪ $e ⟫ f⋆⟪ $t ⟫)
    | `( f⟪ $e₁ + $e₂ ⟫ ) => `(Term.prim f⟪ $e₁ ⟫ Prim.plus f⟪ $e₂ ⟫ )
    | `( f⟪ $e₁ - $e₂ ⟫ ) => `(Term.prim f⟪ $e₁ ⟫ Prim.minus f⟪ $e₂ ⟫ )
    | `( f⟪ $e₁ * $e₂ ⟫ ) => `(Term.prim f⟪ $e₁ ⟫ Prim.times f⟪$e₂ ⟫ )
    | `( f⟪ ($e₁, $e₂) ⟫) => `(Term.pair f⟪ $e₁ ⟫ f⟪$e₂ ⟫ )
    | `( f⟪ π₁ $e ⟫) => `(Term.fst f⟪ $e ⟫ )
    | `( f⟪ π₂ $e ⟫) => `(Term.snd f⟪ $e ⟫ )
    | `( f⟪ if0 $e₁ then $e₂ else $e₃ end ⟫ ) => `(Term.if0 f⟪ $e₁ ⟫ f⟪ $e₂ ⟫ f⟪ $e₃ ⟫ )
    | `( f⟪ if0 ($e₁, $e₂, $e₃) ⟫ ) => `(Term.if0 f⟪ $e₁ ⟫ f⟪ $e₂ ⟫ f⟪ $e₃ ⟫ )

    | `( f⟪ ( $e ) ⟫ ) => `(f⟪ $e ⟫) 

    def repr : (Γ ⊢F t) → String
      | .int i => i.repr
      | .unit => "()"
      | .var x => x.repr

      | .fix e => s!"(λ. {e.repr})"
      | .app e₁ e₂ => s!"{e₁.repr} {e₂.repr}"

      | _ => "in progress"
end Term
open Term

instance : Repr (Γ ⊢F t) where
  reprPrec e _ := e.repr

namespace Examples 
  def fact :  ∅ ⊢F f⋆⟪ int → int ⟫ :=
    Term.fix (.if0 (.var .here)
        (.int 1)
        (.prim (.var .here) .times (.app (.var (.there .here)) (Term.prim (.var .here) .minus (.int 1)))))

  def fact' : ∅ ⊢F f⋆⟪ int → int ⟫ := 
    f⟪ λ.
      if0 #0 then
        1
      else
        #0 * (#1 (#0 - 1))
      end ⟫

  theorem fact_eq_fact' : fact = fact' := rfl

  def sixfact := f⟪ !fact 6 ⟫

  def polyid : ∅ ⊢F f⋆⟪ ∀. ♯0 → ♯0 ⟫ :=  
    f⟪ Λ. λ. #0 ⟫

  def intid : ∅ ⊢F f⋆⟪ int → int ⟫ :=
    f⟪ (!polyid)[int] ⟫

  def twice : ∅ ⊢F f⋆⟪ ∀. (♯0 → ♯0) → ♯0 → ♯0 ⟫ := 
    f⟪ Λ. λ. λ. #2 #2 #0 ⟫ 
end Examples

def conv_ent {Δ Γ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : t₁ = t₂ → (Γ ⊢F t₁) → Γ ⊢F t₂
  | rfl, a => a

def Ren {Δ₁ Δ₂} (Γ₁ : Ctx Δ₁) (Γ₂ : Ctx Δ₂) : Renτ Δ₁ Δ₂ → Type := 
  fun rt =>
  ∀ {t : Δ₁ ⊢F⋆ ⋆}, Γ₁ ∋ t → Γ₂ ∋ renτ rt t

def lift {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Renτ Δ₁ Δ₂} (r : Ren Γ₁ Γ₂ rt) {t : Δ₁ ⊢F⋆ ⋆} : 
  Ren (Γ₁ ,, t) (Γ₂ ,, renτ rt t) rt 
  | _, .here => .here
  | _, .there x => .there (r x)

def τlift {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Renτ Δ₁ Δ₂} (r : Ren Γ₁ Γ₂ rt) : 
  ∀ {k}, Ren (Γ₁ ,,⋆ k) (Γ₂ ,,⋆ k) (liftτ rt)
  | _, _, .move x => by
    apply conv_ni
    rotate_left 1
    · exact (Lookup.move (r x))
    · simp [weakenτ]
      repeat rw [←renτ_comp]
      congr


def ren {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Renτ Δ₁ Δ₂} (r : Ren Γ₁ Γ₂ rt) :
  {t : Δ₁ ⊢F⋆ ⋆} → (Γ₁ ⊢F t) → (Γ₂ ⊢F renτ rt t)
  | _, .int i => .int i
  | _, .unit => .unit
  | _, .var x => .var (r x)

  | _, .fix e => .fix (ren (lift (lift r)) e)
  | _, .app e₁ e₂ => .app (ren r e₁) (ren r e₂)

  | _, .Λ e => .Λ (ren (τlift r) e) 
  | _, .sub e t => by
    apply conv_ent; rotate_left 1
    · exact (Term.sub (ren r e) (renτ rt t))
    . rw [renτ_subsτ_one]
  
  | _, .prim e₁ p e₂ => .prim (ren r e₁) p (ren r e₂)
  | _, .pair e₁ e₂ => .pair (ren r e₁) (ren r e₂)
  | _, .fst e => .fst (ren r e)
  | _, .snd e => .snd (ren r e)
  | _, .if0 e₁ e₂ e₃ => .if0 (ren r e₁) (ren r e₂) (ren r e₃)

def weaken {Δ Γ} {t₁ t₂ : Δ ⊢F⋆ ⋆} (e : Γ ⊢F t₁) : (Γ ,, t₂ ⊢F t₁) := by
  apply conv_ent; rotate_left 1
  · exact (ren (conv_ni (Eq.symm renτ_id) ∘ .there) e)
  · apply renτ_id

def tweaken {Δ Γ} (t : Δ ⊢F⋆ ⋆) {k} (e : Γ ⊢F t) : Γ ,,⋆ k ⊢F weakenτ t :=
  ren .move e

def Subs {Δ₁ Δ₂} (Γ₁ : Ctx Δ₁) (Γ₂ : Ctx Δ₂) (st : Subsτ Δ₁ Δ₂) : Type := 
  {t : Δ₁ ⊢F⋆ ⋆} → (Γ₁ ∋ t) → (Γ₂ ⊢F subsτ st t)

def lifts {Δ₁ Δ₂ Γ₁ Γ₂} (st : Subsτ Δ₁ Δ₂) (s : Subs Γ₁ Γ₂ st) {t : Δ₁ ⊢F⋆ ⋆} : Subs (Γ₁ ,, t) (Γ₂ ,, subsτ st t) st
  | _, .here => .var .here
  | _, .there x => weaken (s x)

def tlifts {Δ₁ Δ₂ Γ₁ Γ₂} (st : Subsτ Δ₁ Δ₂) (s : Subs Γ₁ Γ₂ st) : Subs (Γ₁ ,,⋆ k) (Γ₂ ,,⋆ k) (liftsτ st) 
  | t, x => by
    cases x
    rename_i t x
    apply conv_ent; rotate_left 1
    · exact (tweaken _ (s x))
    · simp [weakenτ]
      rw [←renτ_subsτ]
      rw [←subsτ_renτ]
      congr

def subs {Δ₁ Δ₂ Γ₁ Γ₂} (st : Subsτ Δ₁ Δ₂) (s : Subs Γ₁ Γ₂ st) 
  {t : Δ₁ ⊢F⋆ ⋆} : (Γ₁ ⊢F t) → (Γ₂ ⊢F subsτ st t)
  | .int i => .int i
  | .unit => .unit
  | .var x => s x

  | .fix e => .fix (subs st (lifts st (lifts st s)) e)
  | .app e₁ e₂ => .app (subs st s e₁) (subs st s e₂)

  | .Λ e => by
    apply Term.Λ
    rename_i t'
    apply conv_ent; rotate_left 1
    · exact (subs (liftsτ st) (tlifts st s) e)
    · congr
  | .sub e t => by
    apply conv_ent; rotate_left 1
    · exact (Term.sub (subs st s e) (subsτ st t))
    · rw [subsτ_subsτ_one] 

  | .prim e₁ p e₂ => .prim (subs st s e₁) p (subs st s e₂)
  | .pair e₁ e₂ => .pair (subs st s e₁) (subs st s e₂)
  | .fst e => .fst (subs st s e)
  | .snd e => .snd (subs st s e)
  | .if0 e₁ e₂ e₃ => .if0 (subs st s e₁) (subs st s e₂) (subs st s e₃)

def extend {Δ₁ Δ₂ Γ₁ Γ₂} (st : Subsτ Δ₁ Δ₂) (s : Subs Γ₁ Γ₂ st) {t : Δ₁ ⊢F⋆ ⋆} : (Γ₂ ⊢F subsτ st t) → Subs (Γ₁ ,, t) Γ₂ st 
  | e, _, .here => e
  | _, _, .there x => s x

def subs_extend {Δ Γ k} {t₁ : Δ ,⋆ k ⊢F⋆ ⋆} {t₂ : Δ ⊢F⋆ k} (x : Γ ,,⋆ k ∋ t₁): Γ ⊢F subsτ (extendτ .var t₂) t₁ := by
  cases x
  rename_i x
  apply conv_ent; rotate_left 1
  · exact (.var x)
  · simp [weakenτ]
    rw [←subsτ_renτ]
    have : (fun {j} => extendτ (fun {j} => Typ.var) t₂ ∘ Lookupt.there) = fun {j} => @Typ.var Δ j := by
      funext j x
      cases x <;> rfl
    rw [this, subsτ_id]

def subs_one {Δ Γ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : (Γ ,, t₂ ⊢F t₁) → (Γ ⊢F t₂) → (Γ ⊢F t₁) := by
  intro e₂ e₁
  apply conv_ent; rotate_left 1
  · exact (subs .var
      (extend .var
       (conv_ent (Eq.symm (subsτ_id _)) ∘ .var)
       (conv_ent (Eq.symm (subsτ_id t₂)) e₁))
      e₂)
  · rw [subsτ_id]

macro b:term:80 ".[" a:term:80 "]" : term =>
  `(subs_one $b $a)

def tsubs_one {Δ Γ k} {t₁ : Δ ,⋆ k ⊢F⋆ ⋆} (e : Γ ,,⋆ k ⊢F t₁) (t₂ : Δ ⊢F⋆ k) : Γ ⊢F (t₁[t₂]⋆) := subs (extendτ .var t₂) subs_extend e

macro b:term:80 "⋆[" a:term:80 "]" : term =>
  `(tsubs_one $b $a)

example : (f⟪ #0 ⟫.[f⟪ (1, 2) ⟫] : ∅ ⊢F f⋆⟪ int × int ⟫) =
           f⟪ (1, 2) ⟫                                  := rfl

example : (f⟪ λ. #1 #0 ⟫.[f⟪ (6, 9) ⟫] : ∅ ⊢F f⋆⟪ int → int ⟫) =
           f⟪ λ. #1 #0 ⟫                                      := rfl
