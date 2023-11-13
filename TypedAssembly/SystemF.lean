import «TypedAssembly».Util 

import Std.Data.List.Basic
import Lean.Data.AssocList
open Lean (AssocList)

structure TypVar where
  a : String
  deriving Repr, BEq, DecidableEq

instance : Coe String TypVar where
  coe x := ⟨x⟩ 

structure TermVar where
  x : String
  deriving Repr, BEq, DecidableEq

instance : Coe String TermVar where
  coe x := ⟨x⟩ 

inductive Prim where
  | plus
  | minus
  | times
  deriving Repr, BEq

inductive Typ where
  | int                              
  | var (a : TypVar)              
  | arrow (t₁ : Typ) (t₂ : Typ)  
  | for_all (a : TypVar) (t : Typ)    
  deriving Repr, BEq

declare_syntax_cat typ
syntax str : typ
syntax:10 "All " str ". " typ : typ
syntax:50 typ " -> " typ : typ
syntax:50 ident " -> " ident : typ
syntax " int " : typ
syntax " t⟪ " typ " ⟫ " : term

syntax " ( " typ " ) " : typ

macro_rules 
  | `( t⟪ int ⟫ ) => `(Typ.int)
  | `( t⟪ $s:str ⟫ ) => `(Typ.var $s)
  | `( t⟪ $t₁:typ -> $t₂:typ ⟫ ) => `(Typ.arrow t⟪ $t₁ ⟫ t⟪ $t₂ ⟫)
  | `( t⟪ $t₁:ident -> $t₂:ident ⟫ ) => `(Typ.arrow $t₁ $t₂)
  | `( t⟪ All $a:str . $t:typ ⟫) => `(Typ.for_all $a t⟪ $t ⟫)
  | `( t⟪ ⟨ $[$t],* ⟩ ⟫ ) => `(Typ.tuple [ $[ t⟪ $t ⟫ ],*])
  | `( t⟪ ( $t )  ⟫ ) => `(t⟪ $t ⟫)

@[simp]
def Typ.free : Typ → List TypVar
  | .int => []
  | .var a => [a]
  | .arrow t₁ t₂ => t₁.free.union t₂.free
  | .for_all a t => List.diff t.free [a]


#eval t⟪ All "a".  "a" -> "a" ⟫.free

@[simp]
def Typ.subst : Typ → Typ → TypVar → Typ 
  | .int, _, _ => .int
  | t@(.var a), t', a' => 
    if a == a' then t' else t
  | _, _, _ => _

inductive Term where
  | var (x : TermVar)
  | int (i : Int)
  | fix (x : TermVar) (x₁ : TermVar) (t₁ : Typ) (t₂ : Typ) (e : Term)
  | app (e₁ : Term) (e₂ : Term)
  | Λ (a : TypVar) (e : Term)
  | sub (e : Term) (t : Typ)
  | prim (e₁ : Term) (p : Prim) (e₂ : Term)
  | if0 (e₁ : Term) (e₂ : Term) (e₂ : Term)
  | ann (u : Term) (t : Typ)
  deriving Repr, BEq


declare_syntax_cat trm
syntax num : trm 
syntax str : trm
syntax " fix " str "( " str " : " typ " ) " " : "  typ ". " trm : trm
syntax " fix " ident "( " ident " : " ident " ) " " : " ident ". " ident : trm
syntax trm trm : trm
syntax " \\ " str ". " trm : trm
syntax trm "[ " typ " ] " : trm
syntax:20 trm:20 " + " trm:21 : trm
syntax:20 trm:20 " - " trm:21 : trm
syntax:30 trm:30 " * " trm:31 : trm
syntax "if0 " " ( " trm " , " trm " , " trm " ) " : trm
syntax trm " as " typ : trm
syntax ident " as " ident : trm
syntax ident " as " typ : trm
syntax trm " as " ident : trm

syntax " ( " trm " ) " : trm

syntax " ⟪ " trm " ⟫" : term

macro_rules
  | `( ⟪ $s:str ⟫ ) => `(Term.var $s)
  | `( ⟪ $i:num ⟫ ) => `(Term.int $i)
  | `( ⟪ fix $x:str ($x₁:str : $t₁:typ) : $t₂:typ . $e:trm ⟫ ) => `(Term.fix $x $x₁ t⟪ $t₁ ⟫ t⟪ $t₂ ⟫ ⟪ $e ⟫)
  | `( ⟪ fix $x:ident ($x₁:ident : $t₁:ident) : $t₂:ident. $e:ident ⟫) => `(Term.fix $x $x₁ $t₁ $t₂ $e)
  | `( ⟪ $e₁ $e₂  ⟫) => `(Term.app ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ )
  | `( ⟪ \ $a. $e ⟫ ) => `(Term.Λ $a ⟪ $e ⟫ )
  | `( ⟪ $e[$t] ⟫ ) => `(Term.sub ⟪ $e ⟫ t⟪ $t ⟫)
  | `( ⟪ $e₁ + $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.plus ⟪ $e₂ ⟫ )
  | `( ⟪ $e₁ - $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.minus ⟪ $e₂ ⟫ )
  | `( ⟪ $e₁ * $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.times ⟪$e₂ ⟫ )
  | `( ⟪ if0($e₁, $e₂, $e₃) ⟫ ) => `(Term.if0 ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ ⟪ $e₃ ⟫ )
  | `( ⟪ $e:trm as $t:typ ⟫ ) => `(Term.ann ⟪ $e ⟫ t⟪ $t ⟫)
  | `( ⟪ $e:ident as $t:ident ⟫ ) => `(Term.ann $e $t )
  | `( ⟪ $e:ident as $t:typ ⟫) => `(Term.ann $e t⟪ $t ⟫ )
  | `( ⟪ $e:trm as $t:ident ⟫ ) => `(Term.ann ⟪ $e ⟫ $t )

  | `( ⟪ ( $e ) ⟫ ) => `( ⟪ $e ⟫ )

@[simp]
def Term.free : Term → List TermVar
  | .var x => [x]
  | .int _ => []
  | .fix x x₁ _ _ e => e.free.diff [x, x₁]
  | .app e₁ e₂ => e₁.free.union e₂.free
  | .Λ _ e => e.free
  | .sub e _ => e.free
  | .prim e₁ _ e₂ => e₁.free.union e₂.free
  | .if0 e₁ e₂ e₃ => e₁.free.union (e₂.free.union e₃.free)
  | .ann u _ => u.free

def sixfact := ⟪ (fix "f" ("n":int):int.
                      if0("n", 1,
                      "n" * ("f" ("n" - 1)))) 6 ⟫


#eval sixfact

def polyid := ⟪ \"a". fix "_" ("x":"a"):"a". "x" ⟫ 
#eval polyid

def polyidtyp := t⟪ All "a". "a" -> "a" ⟫
#eval polyidtyp

def two := ⟪ (fix "y" ("x" : int):int. "x" + 1) 1 ⟫
#eval two


structure Ctx where
  Δ : List TypVar
  Γ : AssocList TermVar Typ 

namespace Ctx 
  def empty : Ctx := ⟨[], .nil⟩ 

  def check_typvar (ctx : Ctx) (a : TypVar) : M Unit :=
    if List.elem a ctx.Δ then pure ()
    else throw s!"TypVar {a.a} not found"
  
  @[simp]
  def lookup_termvar (ctx : Ctx) (x : TermVar) : M Typ := 
    match ctx.Γ.find? x with
    | some t => pure t
    | none => throw s!"TermVar {x.x} not found"

  def extend_Γ (ctx : Ctx) (x : TermVar) (t : Typ) : Ctx :=
    { ctx with Γ := .cons x t ctx.Γ }

  def extend_Δ (ctx : Ctx) (a : TypVar) : Ctx :=
    { ctx with Δ := a :: ctx.Δ }

  def check_typ (ctx : Ctx) : Typ → M Unit
    | .int => pure ()
    | .var a => check_typvar ctx a
    | .arrow t₁ t₂ => do
        check_typ ctx t₁
        check_typ ctx t₂
    | .for_all a t => check_typ (ctx.extend_Δ a) t
end Ctx

inductive DeltaShows : Ctx → Typ → Prop
  | ftv : ∀ {c t}, subset t.free c.Δ → DeltaShows c t

theorem any_ctx_shows_int : forall c, DeltaShows c .int := by
  intros c
  constructor
  simp [Typ.free, subset]

inductive HasType : Ctx → Term → Typ → Prop
  | var : ∀ {c t x}, 
    DeltaShows c t →
    c.lookup_termvar v = .ok t → HasType c (.var x) t
  | int : ∀ {i c}, HasType c (.int i) .int
  | fix : ∀ {c x x₁ t₁ t₂ e}, 
    DeltaShows c t₁ → DeltaShows c t₂ →  
    ¬c.Γ.contains x → ¬c.Γ.contains x₁ → 
    HasType (Ctx.extend_Γ (Ctx.extend_Γ c x₁ t₁) x t⟪ t₁ -> t₂ ⟫) e t₂ →
    HasType c ⟪ fix x (x₁:t₁):t₂. e ⟫ t⟪ t₁ -> t₂ ⟫
  | app : ∀ {c e₁ e₂ t₁ t₂},
    DeltaShows c t₁ → DeltaShows c t₂ → 
    HasType c e₁ t⟪ t₁ -> t₂ ⟫ → HasType c e₂ t₁ → 
    HasType c (.app e₁ e₂) t₂
  | Λ : ∀ {c a e t},
    DeltaShows c t → c.Δ.notElem a → 
    HasType (c.extend_Δ a) e t → 
    HasType c (.Λ a e) (.for_all a t)
  | sub : ∀ {c a e t t'},
    DeltaShows c t → HasType c e (.for_all a t') → 
    HasType c (.sub e t) (t'.subst t a)
  | prim : ∀ {c e₁ e₂ p},
    HasType c e₁ .int → HasType c e₂ .int →
    HasType c (.prim e₁ p e₂) .int
  | if0 : ∀ {c e₁ e₂ e₃ t},
    DeltaShows c t → HasType c e₁ .int → 
    HasType c e₂ t → HasType c e₃ t →
    HasType c (.if0 e₁ e₂ e₃) t

theorem sixfact_has_type_int : HasType Ctx.empty sixfact .int :=
by
  apply HasType.app 
  case t₁ => apply Typ.int
  · apply any_ctx_shows_int
  · apply any_ctx_shows_int
  · constructor <;> try (apply any_ctx_shows_int)
    · simp [AssocList.contains] 
    · simp [AssocList.contains] 
    · constructor
      · constructor
        simp [Typ.free]
      · constructor
        · constructor
          simp [Typ.free, List.Subset]
        case a.a.a.v => exact ⟨"n"⟩
        · rfl
      · constructor
      · constructor
        · constructor
          · constructor
            simp [Typ.free, List.Subset]
          case a.a.a.a.v => exact ⟨"n"⟩ 
          · rfl
        · constructor
          case a.a.a.a.t₁ => exact .int
          · apply any_ctx_shows_int
          · apply any_ctx_shows_int
          · constructor
            · constructor
              · simp [Typ.free, List.Subset]
            case a.a.a.a.a.v => exact ⟨"f"⟩
            · rfl
          · constructor
            · constructor
              · apply any_ctx_shows_int
              case a.a.a.a.a.a.v => exact ⟨"n"⟩
              · rfl
            · constructor
  · constructor   


def Term.typcheck (ctx : Ctx) (e : Term) : {{ typ | HasType ctx e typ }} := 
  match e with
  | .int i => .found .int (by constructor)
  | .var x => by
    cases h : (ctx.lookup_termvar x)
    case ok t => 
      if h' : subset t.free ctx.Δ then
        apply Maybe.found
        case a => exact t
        · constructor
          · constructor
            assumption 
          case a.v => exact x
          · assumption
      else apply Maybe.unknown
    case error => apply Maybe.unknown
  |  ⟪ fix x (x₁:t₁):t₂. e ⟫ => by
    if h₁ : subset t₁.free ctx.Δ then
      if h₂ : subset t₂.free ctx.Δ then
        if h₃ : ¬ ctx.Γ.contains x then
          if h₄ : ¬ctx.Γ.contains x₁ then
            match e.typcheck ((ctx.extend_Γ x₁ t₁).extend_Γ x t⟪ t₁ -> t₂ ⟫) with 
            | .found t p => 
              if h₅ : t == t₂ then
                apply Maybe.found
                case a => exact t⟪ t₁ -> t₂ ⟫
                · apply HasType.fix
                  · constructor; assumption
                  · constructor; assumption
                  · assumption
                  · assumption
                  · rw [beq_iff_eq] at h₅
                    subst t; assumption
                    sorry
                else apply Maybe.unknown 
            | .unknown => apply Maybe.unknown
          else apply Maybe.unknown
        else apply Maybe.unknown
      else apply Maybe.unknown
    else apply Maybe.unknown
              

/-
def typcheck (ctx : Ctx) (e : Term) : M Term :=
  match e with
  | .var x => do
    let typ ← ctx.lookup_termvar x
    pure $ .ann e typ
  | .int _ => pure $ ⟪ e as int ⟫
  | ⟪ fix x (x₁:t₁):t₂. e ⟫ => do
    ctx.check_typ t₁ 
    ctx.check_typ t₂ 
    let ae ← typcheck ((ctx.extend_Γ x t⟪ t₁ -> t₂ ⟫).extend_Γ x₁ t₁) e
    match ae with
    | .ann _ t₂' => 
      if t₂ != t₂' then throw s!"Fix: Types don't match"
      else pure $ ⟪ (fix x (x₁:t₁):t₂. ae) as (t₁ -> t₂) ⟫
    | _ => throw "Fix: Annotated expression expected"
  | .app e₁ e₂ => do
    let ae₁ ← typcheck ctx e₁
    let ae₂ ← typcheck ctx e₂
    match (ae₁, ae₂) with
    | (.ann _ (.arrow t₁ t₂), .ann _ t₃) =>
      if t₁ == t₃ then 
        pure $ .ann (.app ae₁ ae₂) t₂
      else throw "App: Types don't match"
    | _ => throw "App: weird application"
  | .Λ a e => do
    let ae ← typcheck (ctx.extend_Δ a) e
    match ae with
    | .ann _ t => pure $ .ann (.Λ a ae) (.for_all a t)
    | _ => throw "Λ: Annotated expression expected"
  | .sub e t => do
    let ae ← typcheck ctx e
    match ae with
    | .ann _ t' => 
      if List.elem t ctx.Δ then _
      else _
    | _ => throw "Sub: Annotated expression expected"
  | .tuple es => do
    let aes ← es.mapM (typcheck ctx) 
    let typs ← aes.mapM (fun | (.ann _ t) => pure t
                             | _ => throw "Tuple: Annotated expression expected in the elements")
    pure $ .ann (.tuple aes) (.tuple typs)
  | .pi i e => do
    let ae ← typcheck ctx e
    match ae with
    | .ann _ (.tuple ts) => 
      if h : i.toNat < ts.size then
        pure $ .ann (.pi i ae) ts[i.toNat]
      else throw "Π: Index out of bounds"
    | _ => throw "Π: Weird projection"
  | .prim e₁ p e₂ => do
    let ae₁ ← typcheck ctx e₁
    let ae₂ ← typcheck ctx e₂
    match (ae₁, ae₂) with
    | (.ann _ .int, .ann _ .int) => 
      pure $ .ann (.prim ae₁ p ae₂) .int
    | _ => throw "Prim: weird arithmatic"
  | .if0 e₁ e₂ e₃ => do
    let ae₁ ← typcheck ctx e₁
    let ae₂ ← typcheck ctx e₂
    let ae₃ ← typcheck ctx e₃
    match (ae₁, ae₂, ae₃) with
    | (.ann _ t₁, .ann _ t₂, .ann _ t₃) => 
      if t₁ == .int && t₂ == t₃ then
        pure $ .ann (.if0 ae₁ ae₂ ae₃) t₂
      else 
        throw "If0: Weird if"
    | _ => throw "If0: Annotated expression expected"
  | .ann _ _ => pure e
-/
