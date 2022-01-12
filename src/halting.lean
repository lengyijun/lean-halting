import computability.turing_machine


inductive Λ -- states
| A
| B
| C

inductive Γ -- symbols
| zero
| one

instance Λ.inhabited : inhabited Λ := ⟨Λ.A⟩
instance Γ.inhabited : inhabited Γ := ⟨Γ.zero⟩

-- initial state and empty tape:
def cfg₀ : turing.TM0.cfg Γ Λ := turing.TM0.init []

-- chainable step function:
def step' (M : turing.TM0.machine Γ Λ) (x : option (turing.TM0.cfg Γ Λ)) :
  option (turing.TM0.cfg Γ Λ) :=
x.bind (turing.TM0.step M)

-- step a given number of times:
def multistep (M : turing.TM0.machine Γ Λ) (n : ℕ) (cfg : turing.TM0.cfg Γ Λ) :
  option (turing.TM0.cfg Γ Λ) :=
step' M^[n] (some cfg)

theorem multistep_none_add {cfg M n m} (hn : multistep M n cfg = none) :
  multistep M (n + m) cfg = none :=
begin
  induction m with m hm,
  { exact hn, },
  { rw [multistep, nat.add_succ, function.iterate_succ_apply', ← multistep, hm],
    refl, },
end

theorem multistep_none_ge {cfg M n} {m ≥ n} (hn : multistep M n cfg = none) :
  multistep M m cfg = none :=
begin
  rw ← nat.add_sub_of_le H,
  exact multistep_none_add hn,
end


def halts (M : turing.TM0.machine Γ Λ) : Prop :=
∃ n, multistep M n cfg₀ = none


-- machine that halts immediately:
def M₁ : turing.TM0.machine Γ Λ
| _ _ := none

theorem M₁_halts_immediately : turing.TM0.step M₁ cfg₀ = none :=
rfl

theorem M₁_halts : halts M₁ :=
⟨1, rfl⟩


-- machine that goes A → B → halt:
def M₂ : turing.TM0.machine Γ Λ
| Λ.A symbol := some ⟨Λ.B, turing.TM0.stmt.write symbol⟩ 
| _ _ := none

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
def M₃ : turing.TM0.machine Γ Λ
| Λ.A symbol := some ⟨Λ.B, turing.TM0.stmt.write symbol⟩
| Λ.B symbol := some ⟨Λ.A, turing.TM0.stmt.write symbol⟩
| _ _ := none

lemma M₃_AB_only {n} : ∃ tape,
  multistep M₃ n cfg₀ = some ⟨Λ.A, tape⟩ ∨ multistep M₃ n cfg₀ = some ⟨Λ.B, tape⟩ :=
begin
  induction n with n hn,
  { existsi _,
    left,
    refl, },
  { cases hn with tape_n hn,
    cases hn; existsi _,
    {
      right,
      rw [multistep, function.iterate_succ_apply', ← multistep, hn, step', option.bind, turing.TM0.step],
      simp,
      existsi _,
      existsi _,
      split; refl, },
    {
      left,
      rw [multistep, function.iterate_succ_apply', ← multistep, hn, step', option.bind, turing.TM0.step],
      simp,
      existsi _,
      existsi _,
      split; refl, },
  },
end

theorem M₃_not_halts : ¬ halts M₃ :=
begin
  intro h,
  cases h with n hn,
  cases M₃_AB_only with tape h_tape,
  cases h_tape; {
    rw h_tape at hn,
    exact option.no_confusion hn,
  },
end


-- equivalent definitions of halting, using turing.TM0.eval:

def halts' (M : turing.TM0.machine Γ Λ) : Prop :=
(turing.TM0.eval M []).dom

def halts'' (M : turing.TM0.machine Γ Λ) : Prop :=
turing.TM0.eval M [] ≠ part.none

def halts''' (M : turing.TM0.machine Γ Λ) : Prop :=
∃ x, turing.TM0.eval M [] = part.some x

theorem halts'_iff'' {M} : halts' M ↔ halts'' M :=
begin
  rw [halts'', ne.def, part.eq_none_iff', ← halts'],
  exact not_not.symm,
end

theorem halts''_iff''' {M} : halts'' M ↔ halts''' M :=
part.ne_none_iff

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
