inductive Prim where
  | plus
  | minus
  | times
  deriving Repr, BEq, DecidableEq

abbrev interp : Prim → (Int → Int → Int)
  | .plus => Int.add
  | .minus => Int.sub
  | .times => Int.mul

