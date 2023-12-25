import «TypedAssembly».LambdaF.Step

def NoVar : ∀ {Δ}, Ctx Δ → Prop
  | _, .nil => True
  | _, .snoc_typ _ _ => False
  | _, .snoc_kind Γ _ => NoVar Γ

def no_var : ∀ {Δ Γ}, NoVar Γ → {t : Δ ⊢F⋆ ⋆} → (x : Γ ∋ t) → False := by
  intros Δ Γ nv t x
  induction x <;> contradiction

theorem progress : ∀ {Δ Γ}, NoVar Γ → {t : Δ ⊢F⋆ ⋆} → (e : Γ ⊢F t) →
                   Value e ∨ (∃ e', e ==> e') := by
  intros Δ Γ nv t e
  induction e with
  | «int» => apply Or.inl; constructor
  | var x => cases (no_var nv x)
  | fix => apply Or.inl; constructor
  | app e₁ e₂ e₁_ih e₂_ih => 
    apply Or.inr
    have e₁_ih' := e₁_ih nv; clear e₁_ih
    have e₂_ih' := e₂_ih nv; clear e₂_ih
    rename_i Δ' Γ' t₁ t₂
    cases e₁_ih' with
    | inl hv₁ =>
      cases e₂_ih' with
      | inl hv₂ =>
        cases hv₁
        rename_i e''
        exists (e''.[weaken e₂].[.fix e''])
        constructor <;> assumption
      | inr hs =>
        cases hs
        rename_i es s
        exists (.app e₁ es)
        constructor <;> assumption
    | inr hs =>
      cases hs 
      rename_i es e
      exists (.app es e₂)
      constructor <;> assumption
  | Λ e' e'_ih => 
    have e'_ih' := e'_ih nv; clear e'_ih
    cases e'_ih'
    · apply Or.inl
      constructor; assumption
    · apply Or.inr
      rename_i e's
      cases e's
      rename_i e' w
      exists (.Λ e')
      constructor; assumption
  | sub e' t' e'_ih => 
    have e'_ih' := e'_ih nv; clear e'_ih
    apply Or.inr
    cases e'_ih' with
    | inl hv =>
      cases hv
      rename_i e' hv'
      exists (e'⋆[t'])
      constructor <;> assumption
    | inr hs =>
      cases hs
      rename_i es s
      exists (.sub es t')
      constructor <;> assumption
  | prim e₁ p e₂ e₁_ih e₂_ih =>
    have e₁_ih' := e₁_ih nv; clear e₁_ih
    have e₂_ih' := e₂_ih nv; clear e₂_ih
    apply Or.inr
    cases e₁_ih' with
    | inl hv₁ =>
      cases e₂_ih' with
      | inl hv₂ =>
        cases hv₁
        rename_i i₁
        cases hv₂
        rename_i i₂
        exists (.int (interp p i₁ i₂))
        constructor
      | inr hs =>
        cases hs
        rename_i es s
        exists (.prim e₁ p es)
        cases hv₁
        rename_i i₁
        constructor; assumption
    | inr hs =>
      cases hs
      rename_i es s
      exists (.prim es p e₂)
      constructor <;> assumption
  | pair e₁ e₂ e₁_ih e₂_ih => 
    have e₁_ih' := e₁_ih nv; clear e₁_ih
    have e₂_ih' := e₂_ih nv; clear e₂_ih
    cases e₁_ih' with
    | inl hv₁ =>
      cases e₂_ih' with
      | inl hv₂ =>
        apply Or.inl
        constructor <;> assumption
      | inr hs =>
        cases hs
        rename_i es s
        apply Or.inr
        exists (.pair e₁ es)
        constructor <;> assumption
    | inr hs =>
      cases hs
      rename_i es s
      apply Or.inr
      exists (.pair es e₂)
      constructor; assumption
  | fst e' e'_ih =>
    have e'_ih' := e'_ih nv; clear e'_ih
    apply Or.inr
    cases e'_ih' with
    | inl hv =>
      cases hv
      rename_i e₁ hv₁ e₂ hv₂
      exists e₁
      constructor
    | inr hs =>
      cases hs
      rename_i es s
      exists (.fst es)
      constructor; assumption
  | snd e' e'_ih => 
    have e'_ih' := e'_ih nv; clear e'_ih
    apply Or.inr
    cases e'_ih' with
    | inl hv =>
      cases hv
      rename_i e₁ hv₁ e₂ hv₂
      exists e₂
      constructor
    | inr hs =>
      cases hs
      rename_i es s
      exists (.snd es)
      constructor; assumption
  | «if0» e₁ e₂ e₃ e₁_ih =>
    apply Or.inr
    have e₁_ih' := e₁_ih nv; clear e₁_ih
    cases e₁_ih' with
    | inl hv =>
      cases hv
      rename_i i
      cases h : i
      · rename_i n
        cases n
        · exists e₂
          constructor
        · exists e₃
          constructor
          simp [OfNat.ofNat]
      · exists e₃ 
        constructor
        simp [OfNat.ofNat]
    | inr hs =>
      cases hs 
      rename_i es s
      exists (.if0 es e₂ e₃)
      constructor; assumption
