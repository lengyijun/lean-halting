import Mathlib.Computability.TuringMachine

inductive Λ -- states
| A
| B
| C

inductive Γ -- symbols
| zero
| one

instance : Inhabited Λ := ⟨Λ.A⟩
instance : Inhabited Γ := ⟨Γ.zero⟩

-- initial state and empty tape:
def cfg₀ : Turing.TM0.Cfg Γ Λ := Turing.TM0.init []

-- chainable step function:
def step' (M : Turing.TM0.Machine Γ Λ) (x : Option (Turing.TM0.Cfg Γ Λ)) :
  Option (Turing.TM0.Cfg Γ Λ) :=
x.bind (Turing.TM0.step M)

-- step a given number of times:
def multistep (M : Turing.TM0.Machine Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
  Option (Turing.TM0.Cfg Γ Λ) :=
(step' M)^[n] (some cfg)

theorem multistep_none_add {cfg M n m} (hn : multistep M n cfg = none) :
  multistep M (n + m) cfg = none := by
  induction m
  . exact hn
  . rw [multistep, Nat.add_succ, Function.iterate_succ_apply', ← multistep]
    simp [*]
    rfl

theorem multistep_none_ge {cfg M n} {mn : m ≥ n} (hn : multistep M n cfg = none) :
  multistep M m cfg = none := by
rw [← Nat.add_sub_of_le mn]
exact multistep_none_add hn


def halts (M : Turing.TM0.Machine Γ Λ) : Prop :=
∃ n, multistep M n cfg₀ = none


-- machine that halts immediately:
def M₁ : Turing.TM0.Machine Γ Λ
| _, _ => none

theorem M₁_halts_immediately : Turing.TM0.step M₁ cfg₀ = none :=
rfl

theorem M₁_halts : halts M₁ :=
⟨1, rfl⟩


-- machine that goes A → B → halt:
def M₂ : Turing.TM0.Machine Γ Λ
| Λ.A, symbol => some ⟨Λ.B, Turing.TM0.Stmt.write symbol⟩
| _, _        => none

-- step 0, Λ.A:
#reduce multistep M₂ 0 cfg₀
-- step 1, Λ.B:
#reduce multistep M₂ 1 cfg₀
-- step 2, halt:
#reduce multistep M₂ 2 cfg₀
-- step 3, still halted:
#reduce multistep M₂ 3 cfg₀

theorem M₂_halts : halts M₂ :=
⟨2, rfl⟩


-- machine that loops A → B → A → B → ⋯:
def M₃ : Turing.TM0.Machine Γ Λ
| Λ.A, symbol => some ⟨Λ.B, Turing.TM0.Stmt.write symbol⟩
| Λ.B, symbol => some ⟨Λ.A, Turing.TM0.Stmt.write symbol⟩
| _, _ => none

lemma M₃_AB_only {n} : ∃ tape,
  multistep M₃ n cfg₀ = some ⟨Λ.A, tape⟩ ∨ multistep M₃ n cfg₀ = some ⟨Λ.B, tape⟩ := by
induction n with
| zero => exists (Turing.Tape.mk₁ [])
          left
          rfl
| succ n => rename_i hn
            cases hn
            rename_i tape_n hn
            exists tape_n
            cases hn <;> rename_i hn
            . right
              rw [multistep, Function.iterate_succ_apply', ← multistep, hn, step', Option.bind, Turing.TM0.step]
              tauto
            . left
              rw [multistep, Function.iterate_succ_apply', ← multistep, hn, step', Option.bind, Turing.TM0.step]
              tauto

theorem M₃_not_halts : ¬ halts M₃ := by
  rintro ⟨n, hn⟩
  have ⟨tape, h_tape⟩ := @M₃_AB_only n
  cases h_tape with
  | inl h_tape => rw [h_tape] at hn
                  tauto
  | inr h_tape => rw [h_tape] at hn
                  tauto


-- equivalent definitions of halting, using turing.TM0.eval:

def halts' (M : Turing.TM0.Machine Γ Λ) : Prop :=
(Turing.TM0.eval M []).Dom

def halts'' (M : Turing.TM0.Machine Γ Λ) : Prop :=
Turing.TM0.eval M [] ≠ Part.none

def halts''' (M : Turing.TM0.Machine Γ Λ) : Prop :=
∃ x, Turing.TM0.eval M [] = Part.some x

theorem halts'_iff'' {M} : halts' M ↔ halts'' M :=
begin
  rw [halts'', ne.def, part.eq_none_iff', ← halts'],
  exact not_not.symm,
end

theorem halts''_iff''' {M} : halts'' M ↔ halts''' M :=
Part.ne_none_iff

theorem halts_iff' {M} : halts M ↔ halts' M :=
begin
  -- proof by Mario Carneiro …I don't undertand it all
  rw [halts, halts'],
  simp [turing.TM0.eval, cfg₀, multistep],
  split,
  { rintro ⟨n, e⟩,
    generalize_hyp : turing.TM0.init [] = k at e ⊢,
    induction n with n IH generalizing k, {cases e},
    rw [nat.iterate, step', option.bind] at e,
    cases e' : turing.TM0.step M k; rw e' at e,
    { exact part.dom_iff_mem.2 ⟨_, turing.mem_eval.2 ⟨relation.refl_trans_gen.refl, e'⟩⟩ },
    { rw turing.reaches_eval (relation.refl_trans_gen.single e'),
      exact IH _ e } },
  { intro h,
    obtain ⟨a, h⟩ := part.dom_iff_mem.1 h,
    refine turing.eval_induction h (λ k h IH, _),
    cases e : turing.TM0.step M k,
    { exact ⟨1, e⟩ },
    { obtain ⟨n, hn⟩ := IH _ _ e,
      { exact ⟨n+1, by simp [nat.iterate, step', e, hn]⟩ },
      { rwa ← turing.reaches_eval (relation.refl_trans_gen.single e) } } }
end


theorem M₁_halts' : halts' M₁ :=
begin
  rw [halts', turing.TM0.eval, part.map_dom, part.dom_iff_mem],
  existsi _,
  rw turing.mem_eval,
  exact ⟨relation.refl_trans_gen.refl, rfl⟩,
end

theorem M₁_halts'' : halts'' M₁ :=
halts'_iff''.mp M₁_halts'

theorem M₁_halts''' : halts''' M₁ :=
halts''_iff'''.mp M₁_halts''


theorem M₂_halts' : halts' M₂ :=
begin
  rw [halts', turing.TM0.eval, part.map_dom, part.dom_iff_mem],
  existsi turing.TM0.cfg.mk Λ.B (turing.tape.mk₁ []),
  rw turing.mem_eval,
  split,
  { sorry, },
  { refl, },
end
