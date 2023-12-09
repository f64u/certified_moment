import «TypedAssembly».SystemF.TermNf

def RenNf {Δ₁ Δ₂} (Γ₁ : CtxNf Δ₁) (Γ₂ : CtxNf Δ₂) : Rent Δ₁ Δ₂ → Type := 
  fun rt =>
  ∀ {t : Δ₁ ⊢nf⋆ ⋆}, Γ₁ ∋nf t → Γ₂ ∋nf rent_nf rt t

def lift_nf {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Rent Δ₁ Δ₂} (r : RenNf Γ₁ Γ₂ rt) {t : Δ₁ ⊢nf⋆ ⋆} : 
  RenNf (Γ₁ ,, t) (Γ₂ ,, rent_nf rt t) rt 
  | _, .here => .here
  | _, .there x => .there (r x)

def tlift_nf {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Rent Δ₁ Δ₂} (r : RenNf Γ₁ Γ₂ rt) : 
  ∀ {k}, RenNf (Γ₁ ,,⋆ k) (Γ₂ ,,⋆ k) (liftt rt)
  | _, _, .move x => by
    apply conv_ni_nf
    any_goals (exact (LookupNf.move (r x)))
    simp [weakent_nf]
    repeat rw [←rent_nf_comp]
    congr

def ren_nf {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Rent Δ₁ Δ₂} (r : RenNf Γ₁ Γ₂ rt) :
  {t : Δ₁ ⊢nf⋆ ⋆} → (Γ₁ ⊢nf t) → (Γ₂ ⊢nf rent_nf rt t)
  | _, .int i => .int i
  | _, .var x => .var (r x)

  | _, .fix e => .fix (ren_nf (lift_nf (lift_nf r)) e)
  | _, .app e₁ e₂ => .app (ren_nf r e₁) (ren_nf r e₂)

  | _, .Λ e => .Λ (ren_nf (tlift_nf r) e) 
  | _, .sub e t => by
    apply conv_ent_nf 
    any_goals (exact (TermNf.sub (ren_nf r e) (rent_nf rt t)))
    rw [rent_subst_nf_one]
  
  | _, .prim e₁ p e₂ => .prim (ren_nf r e₁) p (ren_nf r e₂)
  | _, .pair e₁ e₂ => .pair (ren_nf r e₁) (ren_nf r e₂)
  | _, .fst e => .fst (ren_nf r e)
  | _, .snd e => .snd (ren_nf r e)
  | _, .if0 e₁ e₂ e₃ => .if0 (ren_nf r e₁) (ren_nf r e₂) (ren_nf r e₃)

def weaken_nf {Δ Γ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} (e : Γ ⊢nf t₁) : (Γ ,, t₂ ⊢nf t₁) := conv_ent_nf rent_nf_id (ren_nf (conv_ni_nf (Eq.symm rent_nf_id) ∘ .there) e)

def tweaken_nf {Δ Γ} (t : Δ ⊢nf⋆ ⋆) {k} (e : Γ ⊢nf t) : Γ ,,⋆ k ⊢nf weakent_nf t :=
  ren_nf .move e

def SubsNf {Δ₁ Δ₂} (Γ₁ : CtxNf Δ₁) (Γ₂ : CtxNf Δ₂) (st : SubstNf Δ₁ Δ₂) : Type := 
  {t : Δ₁ ⊢nf⋆ ⋆} → (Γ₁ ∋nf t) → (Γ₂ ⊢nf subst_nf st t)

def lifts_nf {Δ₁ Δ₂ Γ₁ Γ₂} (st : SubstNf Δ₁ Δ₂) (s : SubsNf Γ₁ Γ₂ st) {t : Δ₁ ⊢nf⋆ ⋆} :
  SubsNf (Γ₁ ,, t) (Γ₂ ,, subst_nf st t) st
  | _, .here => .var .here
  | _, .there x => weaken_nf (s x)

def tlifts_nf {Δ₁ Δ₂ Γ₁ Γ₂} (st : SubstNf Δ₁ Δ₂) (s : SubsNf Γ₁ Γ₂ st) : SubsNf (Γ₁ ,,⋆ k) (Γ₂ ,,⋆ k) (liftst_nf st) 
  | t, x => by
    cases x
    rename_i t x
    exact (conv_ent_nf (weakent_subst_nf st t) (tweaken_nf _ (s x)))

def subs_nf {Δ₁ Δ₂ Γ₁ Γ₂} (st : SubstNf Δ₁ Δ₂) (s : SubsNf Γ₁ Γ₂ st) 
  {t : Δ₁ ⊢nf⋆ ⋆} : (Γ₁ ⊢nf t) → (Γ₂ ⊢nf subst_nf st t)
  | .int i => .int i
  | .var x => s x

  | .fix e => .fix (subs_nf st (lifts_nf st (lifts_nf st s)) e)
  | .app e₁ e₂ => .app (subs_nf st s e₁) (subs_nf st s e₂)

  | .Λ e => by
    apply TermNf.Λ
    rename_i t'
    exact (conv_ent_nf (subst_liftt_nf st t')
              (subs_nf (liftst_nf st) (tlifts_nf st s) e))
  | .sub e t => by
    apply conv_ent_nf
    any_goals (exact (TermNf.sub (subs_nf st s e) (subst_nf st t)))
    rw [subst_subst_nf_one]
    simp [reify]

  | .prim e₁ p e₂ => .prim (subs_nf st s e₁) p (subs_nf st s e₂)
  | .pair e₁ e₂ => .pair (subs_nf st s e₁) (subs_nf st s e₂)
  | .fst e => .fst (subs_nf st s e)
  | .snd e => .snd (subs_nf st s e)
  | .if0 e₁ e₂ e₃ => .if0 (subs_nf st s e₁) (subs_nf st s e₂) (subs_nf st s e₃)

def extend_nf {Δ₁ Δ₂ Γ₁ Γ₂} (st : SubstNf Δ₁ Δ₂) (s : SubsNf Γ₁ Γ₂ st) {t : Δ₁ ⊢nf⋆ ⋆} : (Γ₂ ⊢nf subst_nf st t) → SubsNf (Γ₁ ,, t) Γ₂ st 
  | e, _, .here => e
  | _, _, .there x => s x

def subs_extend : ∀ {Δ Γ k} {t₁ : Δ ,⋆ k ⊢nf⋆ ⋆} {t₂ : Δ ⊢nf⋆ k} (x : Γ ,,⋆ k ∋nf t₁), Γ ⊢nf subst_nf (extendt_nf (.ne ∘ .var) t₂) t₁ := by
  intros
  rename_i x
  cases x
  rename_i x
  exact (conv_ent_nf (weakent_subst_nf_one _ _) (.var x))


def subs_nf_one {Δ Γ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} : (Γ ,, t₂ ⊢nf t₁) → (Γ ⊢nf t₂) → (Γ ⊢nf t₁) := by
  intro e₂ e₁
  apply conv_ent_nf
  any_goals (exact (subs_nf (.ne ∘ .var) 
                    (extend_nf (.ne ∘ .var)
                     (conv_ent_nf (Eq.symm (subst_nf_id _)) ∘ .var)
                     (conv_ent_nf (Eq.symm (subst_nf_id t₂)) e₁))
                    e₂))
  rw [subst_nf_id]

macro b:term:80 "[" a:term:80 "]nf" : term =>
  `(subs_nf_one $b $a)

def tsubs_nf_one {Δ Γ k} (t₁ : Δ ,⋆ k ⊢nf⋆ ⋆) (e : Γ ,,⋆ k ⊢nf t₁) (t₂ : Δ ⊢nf⋆ k) : Γ ⊢nf (t₁[t₂]nf⋆) := subs_nf (extendt_nf (.ne ∘ .var) t₂) subs_extend e

macro b:term:80 "⋆[" a:term:80 "]nf" : term =>
  `(tsubs_nf_one $b $a)


inductive Value : {Δ : Ctxt} → {Γ : CtxNf Δ} → {t : Δ ⊢nf⋆ ⋆} → (Γ ⊢nf t) → Prop where
  | v_int : Value (.int i)
  | v_fix : Value (TermNf.fix e)
  | v_Λ  : Value e → Value (.Λ e)
  | v_pair : Value e₁ → Value e₂ → Value (.pair e₁ e₂)

inductive Step {Δ} {Γ : CtxNf Δ} : (Γ ⊢nf t) → (Γ ⊢nf t) → Prop
  | app_exec : Value a → Step (.app (.fix e) a) ((e[.fix sorry]nf)[a]nf)
  | app_left : Step a a' → Step (.app a e₁) (.app a' e₂)
  | app_right : Value a → Step b b' → Step (.app a b) (.app a b')

  | prim_exec  : Step (.prim (.int n₁) p (.int n₂)) (.int (interp p n₁ n₂))
  | prim_left  : Step a a' → Step (.prim a p b) (.prim a' p b)
  | prim_right : Step b b' → Step (.prim (.int n) p b) (.prim (.int n) p b')

  | fst_exec   : Step nf⟪ π₁(!e, !_) ⟫ e
  | fst_steps  : Step e e' →  Step (.fst e) (.fst e')

  | snd_exec   : Step nf⟪ π₂(!_, !e) ⟫ e
  | snd_steps  : Step e e' →  Step (.snd e) (.snd e')

  | if0_exec   : Step nf⟪ if0 0 then !b else !c end ⟫ b
  | ifn0_exec  : n ≠ 0 → Step nf⟪ if0 !(.int n) then !b else !c end ⟫ c
  | if_steps   : Step a a' → Step nf⟪ if0 !a then !b else !c end ⟫ nf⟪ if0 !a' then !b else !c end ⟫

inductive MultiStep {Δ} {Γ : CtxNf Δ} {t : Δ ⊢nf⋆ ⋆} : (Γ ⊢nf t) → (Γ ⊢nf t) → Prop 
  | refl {a} : MultiStep a a
  | step {a b c} : Step a b → MultiStep b c → MultiStep a c

theorem «1+1 -->* 2» : MultiStep (Γ := ∅) nf⟪ if0 0 then 1 + 1 else 5 end ⟫ nf⟪ 2 ⟫ :=
  by repeat constructor

theorem «fact 6 -->⋆ 720» : MultiStep (Γ := ∅) nf⟪ !fact 6 ⟫ nf⟪ 720 ⟫ := by repeat constructor

