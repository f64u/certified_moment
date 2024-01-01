import «TypedAssembly».Common.Kind

/-- This is essentially a Nat, since we do not gain
    information by cons'ing a specific Kind (they're all ⋆) -/
inductive Ctxt where
  | nil 
  | snoc : Ctxt → Kind → Ctxt
  deriving BEq, DecidableEq, Repr

namespace Ctxt 
  notation "Ø" => Ctxt.nil
  infixl:100 " ,⋆ " => Ctxt.snoc
  
  @[reducible]
  def extend : Ctxt → Ctxt → Ctxt
    | .nil, Δ => Δ
    | .snoc Δ' k, Δ => (Δ'.extend Δ).snoc k

end Ctxt
open Ctxt

/-- This is essentially Fin2 in Lean, for the same reason above --/
inductive Lookupt : Ctxt → Kind → Type where
  | here  {Δ j}   : Lookupt (Δ ,⋆ j) j
  | there {Δ j k} : Lookupt Δ j → Lookupt (Δ ,⋆ k) j
  deriving BEq, DecidableEq


namespace Lookupt 
  infixl:90 " ∋⋆ " => Lookupt

  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic| exact Lookupt.here)
  | n+1 => `(tactic| apply Lookupt.there; get_elem $(Lean.quote n))

  def toNat : Δ ∋⋆ k → Nat 
    | .here => 0
    | .there x => x.toNat + 1

  def repr (x : Δ ∋⋆ k) : String := s!"♯{x.toNat}"

end Lookupt
open Lookupt

instance : Repr (Lookupt Δ k) where
  reprPrec x _ := s!"♯{x.toNat}"

