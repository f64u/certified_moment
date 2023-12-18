import «TypedAssembly»

/-- We do not support higher Typs -/
inductive Kind where
  | star
  deriving BEq, DecidableEq, Repr

namespace Kind 
  notation " ⋆ " => Kind.star
end Kind
open Kind

