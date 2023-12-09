import «TypedAssembly».SystemF.Kind

inductive Ctxt where
  | nil 
  | cons : Ctxt → Kind → Ctxt
  deriving BEq, DecidableEq, Repr

namespace Ctxt 
  notation "Ø" => Ctxt.nil
  infixl:100 " ,⋆ " => Ctxt.cons
end Ctxt
open Ctxt


inductive Lookupt : Ctxt → Kind → Type where
  | here {Δ j} : Lookupt (Δ ,⋆ j) j
  | there {Δ j k} : Lookupt Δ j → Lookupt (Δ ,⋆ k) j
  deriving BEq, DecidableEq, Repr

namespace Lookupt 
  infixl:90 " ∋⋆ " => Lookupt
end Lookupt
open Lookupt

