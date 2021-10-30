import computability.turing_machine

inductive Λ -- states
| A : Λ
| B : Λ
| C : Λ
instance Λ.inhabited : inhabited Λ := ⟨Λ.A⟩

inductive Γ -- symbols
| zero : Γ
| one : Γ
instance Γ.inhabited : inhabited Γ := ⟨Γ.zero⟩

-- initial state and empty tape:
def cfg₀ : turing.TM0.cfg Γ Λ := turing.TM0.init []

-- chainable step function:
def step' (M : turing.TM0.machine Γ Λ) (x : option (turing.TM0.cfg Γ Λ)) : option (turing.TM0.cfg Γ Λ) :=
option.bind x (turing.TM0.step M)

def multistep (M : turing.TM0.machine Γ Λ) (n : ℕ) : option (turing.TM0.cfg Γ Λ) -> option (turing.TM0.cfg Γ Λ) :=
n.repeat $ λ _, step' M

theorem multistep_none_add : ∀ {cfg : turing.TM0.cfg Γ Λ} {M : turing.TM0.machine Γ Λ} {n : ℕ},
multistep M n cfg = none → ∀ { m : ℕ }, multistep M (n + m) cfg = none :=
begin
  intros cfg M n hn m,
  induction m with m hm,
  { exact hn, },
  { rw [multistep, nat.add_succ, nat.repeat, ← multistep, hm],
    refl, },
end

theorem multistep_none_ge : ∀ {cfg : turing.TM0.cfg Γ Λ} {M : turing.TM0.machine Γ Λ} {n : ℕ},
multistep M n cfg = none → ∀ { m ≥ n }, multistep M m cfg = none :=
begin
  intros cfg M n hn m hm,
  rw ← nat.add_sub_of_le hm,
  exact multistep_none_add hn,
end

-- equivalent definitions of halting:
def halts (M : turing.TM0.machine Γ Λ) : Prop :=
∃ n, multistep M n cfg₀ = none

def halts' (M : turing.TM0.machine Γ Λ) : Prop :=
(turing.TM0.eval M []).dom

def halts'' (M : turing.TM0.machine Γ Λ) : Prop :=
turing.TM0.eval M [] ≠ part.none

def halts''' (M : turing.TM0.machine Γ Λ) : Prop :=
∃ x, turing.TM0.eval M [] = part.some x

theorem halts'_iff'' : ∀ {M : turing.TM0.machine Γ Λ}, halts' M ↔ halts'' M :=
begin
  intro M,
  rw [halts'', ne.def, part.eq_none_iff', ← halts'],
  exact not_not.symm,
end

theorem halts''_iff''' : ∀ {M : turing.TM0.machine Γ Λ}, halts'' M ↔ halts''' M :=
λ M, part.ne_none_iff

theorem halts'_iff''' : ∀ {M : turing.TM0.machine Γ Λ}, halts' M ↔ halts''' M :=
λ M, ⟨
  (λ h', halts''_iff'''.mp $ halts'_iff''.mp h'),
  (λ h''', halts'_iff''.mpr $ halts''_iff'''.mpr h''')
⟩


-- machine that halts immediately:
def M1 : turing.TM0.machine Γ Λ
| _ _ := none

#reduce turing.TM0.step M1 cfg₀

theorem M1_halts_immediately : turing.TM0.step M1 cfg₀ = none :=
rfl

#eval turing.TM0.eval M1 []
-- times out:
-- #reduce turing.TM0.eval machine []

theorem M1_halts : halts M1 :=
⟨1, rfl⟩

theorem M1_halts' : halts' M1 :=
begin
  rw [halts', turing.TM0.eval, part.map_dom, part.dom_iff_mem],
  use cfg₀, -- or existsi _ or refine ⟨_, _⟩
  rw turing.mem_eval,
  split,
  { exact relation.refl_trans_gen.refl, },
  { refl, },
end

theorem M1_halts'' : halts'' M1 :=
halts'_iff''.mp M1_halts'

theorem M1_halts''' : halts''' M1 :=
halts''_iff'''.mp M1_halts''


-- machine that goes A → B → halt:
def M2 : turing.TM0.machine Γ Λ
| Λ.A symbol := some ⟨Λ.B, turing.TM0.stmt.write symbol⟩ 
| _ _ := none

-- step 1, Λ.a:
#reduce multistep M2 1 cfg₀
-- step 2, halt:
#reduce multistep M2 2 cfg₀
-- step 3, still halted:
#reduce multistep M2 3 cfg₀

theorem M2_halts : halts M2 :=
⟨2, rfl⟩

theorem M2_halts' : halts' M2 :=
begin
  rw [halts', turing.TM0.eval, part.map_dom, part.dom_iff_mem],
  use cfg₀, -- or existsi _ or refine ⟨_, _⟩
  rw turing.mem_eval,
  split,
  { exact relation.refl_trans_gen.refl, },
  { refl, },
end


-- machine that loops A → B → A → B → ⋯:
def M3 : turing.TM0.machine Γ Λ
| Λ.A symbol := some ⟨Λ.B, turing.TM0.stmt.write symbol⟩
| Λ.B symbol := some ⟨Λ.A, turing.TM0.stmt.write symbol⟩
| _ _ := none