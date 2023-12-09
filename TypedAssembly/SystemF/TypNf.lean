import «TypedAssembly».SystemF.Typ

inductive TypNe : Ctxt → Kind → Type where
  | var : Δ ∋⋆ j → TypNe Δ j
  deriving BEq, DecidableEq, Repr

inductive TypNf : Ctxt → Kind → Type where
  | ne {j}      : TypNe  Δ       j → TypNf Δ j
  | int         : TypNf  Δ       ⋆ 
  | arrow       : TypNf  Δ       ⋆ → TypNf Δ ⋆ → TypNf Δ ⋆
  | prod        : TypNf  Δ       ⋆ → TypNf Δ ⋆ → TypNf Δ ⋆
  | for_all {j} : TypNf (Δ ,⋆ j) ⋆ → TypNf Δ ⋆
  deriving BEq, DecidableEq, Repr

namespace TypNf 
  infixl:90 " ⊢nf⋆ " => TypNf
  infixl:90 " ⊢ne⋆ " => TypNe

  declare_syntax_cat typnf
  syntax "!" term:max : typnf
  syntax:90 "♯" num : typnf
  syntax " int " : typnf
  syntax:50 typnf (" → " <|> " -> ") typnf : typnf
  syntax:50 typnf " × " typnf : typnf
  syntax:10 "∀. " typnf : typnf
  syntax " nf⋆⟪ " typnf " ⟫ " : term

  syntax " ( " typnf " ) " : typnf
  
  macro_rules 
  | `( nf⋆⟪ !$t ⟫) => `($t)
  | `( nf⋆⟪ int ⟫ ) => `(TypNf.int)
  | `( nf⋆⟪ ♯$n ⟫ ) => `(TypNf.ne $ TypNe.var (by get_elem $n))
  | `( nf⋆⟪ $t₁ → $t₂ ⟫ ) => `(TypNf.arrow nf⋆⟪ $t₁ ⟫ nf⋆⟪ $t₂ ⟫)
  | `( nf⋆⟪ $t₁ × $t₂ ⟫ ) => `(TypNf.prod nf⋆⟪ $t₁ ⟫ nf⋆⟪ $t₂ ⟫)
  | `( nf⋆⟪ ∀. $t ⟫) => `(TypNf.for_all nf⋆⟪ $t ⟫)
  | `( nf⋆⟪ ( $t )  ⟫ ) => `(nf⋆⟪ $t ⟫)

  example : Ø ,⋆ ⋆ ,⋆ ⋆ ,⋆ ⋆ ⊢nf⋆ ⋆ := nf⋆⟪ ♯2 ⟫
  def polyidt : Δ ⊢nf⋆ ⋆ := nf⋆⟪ ∀. ♯0 → ♯0 ⟫
end TypNf
open TypNf

def rent_ne {Δ₁ Δ₂} : Rent Δ₁ Δ₂ → ∀ {j}, Δ₁ ⊢ne⋆ j → Δ₂ ⊢ne⋆ j
  | rt, _, .var a => .var (rt a)

def rent_nf {Δ₁ Δ₂} : Rent Δ₁ Δ₂ → ∀ {j}, Δ₁ ⊢nf⋆ j → Δ₂ ⊢nf⋆ j
  |  _, _, .int => .int
  | rt, _, .ne t => .ne $ rent_ne rt t
  | rt, _, .arrow t₁ t₂ => .arrow (rent_nf rt t₁) (rent_nf rt t₂)
  | rt, _, .prod t₁ t₂ => .prod (rent_nf rt t₁) (rent_nf rt t₂)
  | rt, _, .for_all t => .for_all (rent_nf (liftt rt) t)

def weakent_nf {Δ j k} : Δ ⊢nf⋆ j → Δ ,⋆ k ⊢nf⋆ j := rent_nf .there

theorem rent_ne_id : ∀ {Δ j} {t : Δ ⊢ne⋆ j}, rent_ne id t = t := by
  intros Δ j t
  cases t
  rfl

theorem rent_ne_comp : ∀ {Δ₁ Δ₂ Δ₃} {rt₁ : Rent Δ₁ Δ₂} {rt₂ : Rent Δ₂ Δ₃} {j} {t : Δ₁ ⊢ne⋆ j}, rent_ne (rt₂ ∘ rt₁) t = rent_ne rt₂ (rent_ne rt₁ t) := by
  intros Δ₁ Δ₂ Δ₃ rt₁ rt₂ j t
  cases t
  rfl

theorem rent_nf_id : ∀ {Δ j} {t : Δ ⊢nf⋆ j}, rent_nf id t = t := by
  intros Δ j t
  induction t <;> try rfl

  case arrow t₁ t₁_ih t₂ t₂_ih =>
    simp [rent_nf]
    constructor <;> assumption

  case prod t₁ t₁_ih t₂ t₂_ih =>
    simp [rent_nf]
    constructor <;> assumption

  case for_all t' t'_ih =>
    rename_i Δ' j'
    simp [rent_nf]
    have : (fun {j} => @liftt Δ' Δ' id j' j) = (fun {j} => @id (Δ' ,⋆ j' ∋⋆ j)) := by
      funext j a
      apply liftt_id
    rw [this]
    assumption

theorem rent_nf_comp : ∀ {Δ₁ Δ₂ Δ₃} {rt₁ : Rent Δ₁ Δ₂} {rt₂ : Rent Δ₂ Δ₃} {j} {t : Δ₁ ⊢nf⋆ j},
                    rent_nf (rt₂ ∘ rt₁) t = rent_nf rt₂ (rent_nf rt₁ t) := by
  intros Δ₁ Δ₂ Δ₃ rt₁ rt₂ j t
  induction t generalizing Δ₂ Δ₃ rt₂ <;> try rfl

  case arrow t₁ t₂ t₁_ih t₂_ih =>
    rename_i Δ'
    simp [rent_nf]
    constructor <;> simp_all! <;> assumption

  case prod t₁ t₂ t₁_ih t₂_ih =>
    rename_i Δ'
    simp [rent_nf]
    constructor <;> simp_all! <;> assumption

  case for_all t' t'_ih =>
    rename_i Δ' k
    simp [rent_nf]
    have : (fun {j} =>
      @liftt Δ' Δ₃
        (fun {j : Kind} => rt₂ ∘ rt₁) k j) = (fun {j} => liftt rt₂ ∘ liftt rt₁) := by 
        funext _ t
        apply liftt_comp
    rw [this]
    exact (@t'_ih _ _ (liftt rt₁) (liftt rt₂))

-- 3.2
@[reducible]
def SemEnt : Ctxt → Kind → Type
  | Δ, ⋆ => Δ ⊢nf⋆ ⋆

infixl:80 " ⊨ " => SemEnt

def reflect {j Δ} : Δ ⊢ne⋆ j → Δ ⊨ j
  | a => .ne a

def reify {j Δ} : Δ ⊨ j → Δ ⊢nf⋆ j 
  | a => a

def ren_sem {j Δ₁ Δ₂} : Rent Δ₁ Δ₂ → Δ₁ ⊨ j → Δ₂ ⊨ j
  | rt, a => rent_nf rt a

def weaken_sem {j Δ k} : Δ ⊨ j → (Δ ,⋆ k) ⊨ j := ren_sem .there

def Env (Δ₁ Δ₂ : Ctxt) : Type :=
  ∀ {j}, Δ₁ ∋⋆ j → Δ₂ ⊨ j

def extende {Δ₁ Δ₂} : Env Δ₁ Δ₂ → ∀ {j}, Δ₂ ⊨ j → Env (Δ₁ ,⋆ j) Δ₂ 
  | _, _, V, _, .here => V
  | η, _, _, _, .there x => η x
  
def lifte {Δ₁ Δ₂} (η : Env Δ₁ Δ₂) : ∀ {j}, Env (Δ₁ ,⋆ j) (Δ₂ ,⋆ j) :=
  extende (weaken_sem ∘ η) (reflect (.var .here))

def eval {Δ₁ Δ₂ j} : Δ₁ ⊢⋆ j → Env Δ₁ Δ₂ → Δ₂ ⊨ j
  | .int, _ => .int
  | .var x, η => η x
  | .arrow t₁ t₂, η => .arrow (reify (eval t₁ η)) (reify (eval t₂ η))
  | .prod t₁ t₂, η => .prod (reify (eval t₁ η)) (reify (eval t₂ η))
  | .for_all t, η => .for_all (reify (eval t (lifte η)))
 
def id_env (Δ : Ctxt) : Env Δ Δ := reflect ∘ .var

def nf {Δ j} (t : Δ ⊢⋆ j) : Δ ⊢nf⋆ j := reify (eval t (id_env Δ))

-- 3.3
abbrev CR {Δ} k (t₁ t₂ : Δ ⊨ k) : Prop := t₁ = t₂
def reflect_cr {Δ k} {t₁ t₂ : Δ ⊢ne⋆ k} : t₁ = t₂ → CR k (reflect t₁) (reflect t₂) := by simp_all!
def reify_cr {Δ k} (t₁ t₂ : Δ ⊨ k) : CR k t₁ t₂ → reify t₁ = reify t₂ := by simp_all! 
def EnvCr {Δ₁ Δ₂} (η₁ η₂ : Env Δ₁ Δ₂) := ∀ {k} (x : Δ₁ ∋⋆ k), CR k (η₁ x) (η₂ x)

-- 3.4
-- similarly. But we do need to convert from normal forms

@[simp]
def emb_ne {Δ j} : Δ ⊢ne⋆ j → Δ ⊢⋆ j
  | .var x => .var x

def emb_nf {Δ j} : Δ ⊢nf⋆ j → Δ ⊢⋆ j
  | .int => .int
  | .ne t => emb_ne t
  | .arrow t₁ t₂ => .arrow (emb_nf t₁) (emb_nf t₂)
  | .prod t₁ t₂ => .prod (emb_nf t₁) (emb_nf t₂)
  | .for_all t => .for_all (emb_nf t)

-- 3.5
theorem stability : ∀ {Δ j} (t : Δ ⊢nf⋆ j), nf (emb_nf t) = t := by
  intros Δ j t
  induction t <;> try rfl
  case arrow t₁ t₂ t₁_ih t₂_ih =>
    rename_i Δ'
    have : emb_nf (.arrow t₁ t₂) = .arrow (emb_nf t₁) (emb_nf t₂) := by
      rfl
    rw [this]; clear this
    simp [nf, reify]
    have : (eval (Typ.arrow (emb_nf t₁) (emb_nf t₂)) fun {j} => id_env Δ') =
      .arrow (reify (eval (emb_nf t₁) _)) (reify (eval (emb_nf t₂) _)) := by rfl
    rw [this]; clear this
    simp [reify]
    constructor <;> assumption

  case prod t₁ t₂ t₁_ih t₂_ih =>
    rename_i Δ'
    have : emb_nf (.prod t₁ t₂) = .prod (emb_nf t₁) (emb_nf t₂) := by
      rfl
    rw [this]; clear this
    simp [nf, reify]
    have : (eval (Typ.prod (emb_nf t₁) (emb_nf t₂)) fun {j} => id_env Δ') =
      .prod (reify (eval (emb_nf t₁) _)) (reify (eval (emb_nf t₂) _)) := by rfl
    rw [this]; clear this
    simp [reify]
    constructor <;> assumption


  case for_all t' t'_ih =>
    rename_i Δ' k
    simp [nf, reify]

    have : (eval (emb_nf (for_all t')) fun {j} => id_env Δ') = .for_all (reify (eval (emb_nf t') (lifte _))) := rfl
    rw [this]; clear this
    simp 
    conv =>
      rhs
      rw [←t'_ih]
    simp [nf, reify]
    congr
    funext j
    simp [lifte]
    funext x
    unfold extende
    split <;> rfl


-- 3.6
@[reducible]
def SubstNf (Δ₁ Δ₂ : Ctxt) : Type :=
  ∀ {j}, Δ₁ ∋⋆ j → Δ₂ ⊢nf⋆ j

def liftst_nf {Δ₁ Δ₂} : SubstNf Δ₁ Δ₂ → ∀ {j}, SubstNf (Δ₁ ,⋆ j) (Δ₂ ,⋆ j)
  |  _, _, _, .here => .ne $ .var .here
  | st, _, _, .there a => weakent_nf (st a)

def extendt_nf {Δ₁ Δ₂} : SubstNf Δ₁ Δ₂ → ∀ {j}, (Δ₂ ⊢nf⋆ j) → SubstNf (Δ₁ ,⋆ j) Δ₂
  |  _, _, t, _, .here => t
  | st, _, _, _, .there a => st a

def subst_nf {Δ₁ Δ₂} (st : SubstNf Δ₁ Δ₂) {j} (t : Δ₁ ⊢nf⋆ j) : Δ₂ ⊢nf⋆ j := 
  nf (subst (emb_nf ∘ st) (emb_nf t))

def subst_nf_one {Δ j k} (t₁ : Δ ,⋆ k ⊢nf⋆ j) (t₂ : Δ ⊢nf⋆ k) : Δ ⊢nf⋆ j :=
  (subst_nf (extendt_nf (.ne ∘ .var) t₂) t₁)

macro b:term:80 "[" a:term:80 "]nf⋆" : term =>
  `(subst_nf_one $b $a)

example : nf⋆⟪ ♯0 → ♯0 ⟫[.int]nf⋆ = (nf⋆⟪ int → int ⟫ : Ø ⊢nf⋆ ⋆) := rfl

theorem subst_nf_id : ∀ {Δ j} (t : Δ ⊢nf⋆ j), 
                      subst_nf (.ne ∘ .var) t = t := by
  intros Δ j t
  simp [subst_nf]
  have : (fun {j} => (@emb_nf Δ j) ∘ ne ∘ TypNe.var) = fun {j} => Typ.var := by
    funext j x
    cases x <;> rfl
  rw [this]; clear this
  rw [subst_id]
  apply stability

theorem subst_nf_var : ∀ {Δ₁ Δ₂ j} (st : SubstNf Δ₁ Δ₂) (x : Δ₁ ∋⋆ j),
                       subst_nf st (ne (.var x)) = st x := by
  intros 
  apply stability

theorem subst_nf_comp : ∀ {Δ₁ Δ₂ Δ₃} (st₁ : SubstNf Δ₁ Δ₂) (st₂ : SubstNf Δ₂ Δ₃) {j} (t : Δ₁ ⊢nf⋆ j),
                        subst_nf (subst_nf st₂ ∘ st₁) t = subst_nf st₂ (subst_nf st₁ t) := by
  intros Δ₁ Δ₂ Δ₃ st₁ st₂ j t
  unfold subst_nf
  induction t generalizing Δ₂ <;> try rfl

  case ne v =>
    cases v
    simp_all!
    repeat rw [stability]
    
  case arrow Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp_all!
    simp [nf, reify]
    admit

  case prod Δ' t₁ t₂ t₁_ih t₂_ih =>
    simp_all!
    simp [nf, reify]
    admit

  case for_all =>
    admit

theorem rent_subst_nf_one : ∀ {Δ₁ Δ₂ j k} (rt : Rent Δ₁ Δ₂) (t₁ : Δ₁ ,⋆ k ⊢nf⋆ j) (t₂ : Δ₁ ⊢nf⋆ k), rent_nf rt (t₁[t₂]nf⋆) = (rent_nf (liftt rt) t₁)[rent_nf rt t₂]nf⋆ := by

  intros Δ₁ Δ₂ j k rt t₁ t₂

  cases t₁ <;> try rfl 
  case ne t' =>
    cases t'
    rename_i x
    unfold subst_nf_one
    unfold subst_nf
    have : emb_nf (ne (TypNe.var x)) = Typ.var x := by
      rfl
    rw [this]
    cases x <;> try rfl
    simp_all!
    repeat rw [stability]
  
  case arrow t₁ t₂ => 
    admit

  case prod t₁ t₂ => 
    admit

  case for_all t' => 
    admit

theorem weakent_subst_nf : ∀ {Δ₁ Δ₂} (st : SubstNf Δ₁ Δ₂) {k} (t : Δ₁ ⊢nf⋆ ⋆),
                           weakent_nf (subst_nf st t) = subst_nf (liftst_nf st (j := k)) (weakent_nf t) := by 
    admit

theorem subst_liftt_nf : ∀ {Δ₁ Δ₂} (st : SubstNf Δ₁ Δ₂) {k} (t : (Δ₁ ,⋆ k) ⊢nf⋆ ⋆), 
                          subst_nf (liftst_nf st) t =
                          eval (subst (liftst (emb_nf ∘ st)) (emb_nf t)) (lifte (id_env Δ₂)) := by
    admit

theorem subst_subst_nf_one : ∀ {Δ₁ Δ₂ k} (st : SubstNf Δ₁ Δ₂) (t₁ : Δ₁ ⊢nf⋆ k) (t₂ : Δ₁ ,⋆ ⋆ ⊢nf⋆ ⋆),
                              subst_nf st (t₂[t₁]nf⋆) =
                              (eval (subst (liftst (emb_nf ∘ st)) (emb_nf t₂)) (lifte (id_env Δ₂)))[subst_nf st t₁]nf⋆ := by
    admit


theorem weakent_subst_nf_one : ∀ {Δ k} (t₁ : Δ ⊢nf⋆ k) (t₂ : Δ ⊢nf⋆ ⋆),
                               t₂ = (weakent_nf t₂)[t₁]nf⋆ := by admit
