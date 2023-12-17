inductive Prim where
  | plus
  | minus
  | times
  deriving Repr, BEq, DecidableEq

@[reducible, simp]
abbrev interp : Prim → (Int → Int → Int)
  | .plus => Int.add
  | .minus => Int.sub
  | .times => Int.mul

