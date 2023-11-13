
@[reducible]
def M α := Except String α 

inductive Maybe (p : α → Prop) where
  | found : (a : α) → p a → Maybe p
  | unknown

notation "{{ " x " | " p " }}" => Maybe (fun x => p)

def subset {α} [BEq α] (l1 : List α) (l2 : List α) : Bool :=
  l1.all (fun x => l2.elem x)


inductive Vector (α : Type) : Nat → Type where
  | nil : Vector α 0 
  | cons : α → Vector α n → Vector α (Nat.succ n)
  deriving Repr, BEq
