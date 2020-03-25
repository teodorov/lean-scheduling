import data.set.finite data.stream

namespace gtr_cav

open set
--open byte

variables 
    {C : Type} -- configurations
    {A : Type} -- actions
    {R : Type} -- results, events, transition payload
    {P : Type} -- atomic propositions

-- linear blocking semantic transition relation
structure iLSTR :=
    (initial : C)
    (actions : C → A)
    (execute : C → A → option (R × C))
    (one_action : ∀ c, ∃! a, actions c = a)
    (determinist_exe: ∀ c a, ∃! e t, execute c a = some (e, t))

inductive sos_exe  : @iLSTR C A R →  C → C → Prop
notation ⟨ l, ρ₀ ⟩ ` -x→ ` ρ₁ := sos_exe l ρ₀ ρ₁
| step : ∀ (l:@iLSTR C A R) e ρ₀ ρ₁, l.execute ρ₀ (l.actions ρ₀) = some (e, ρ₁)
        → -----------------------------
        ⟨ l, ρ₀ ⟩ -x→ ρ₁

-- deterministic execution semantic transition relation
structure iDESTR := 
    (initial : C)
    (actions : C → set A) 
    (execute : C → A → R × C)
    (determinist_exe : ∀ c a, ∃! e t, execute c a = (e, t))

-- blocking deterministic semantic transition relation
structure iBDSTR := 
    (initial : C)
    (actions : C → set A)
    (execute : C → A → option (R × C))

-- general semantic transition relation
structure iSTR :=
    (initial : set C)
    (actions : C → set A) 
    (execute : C → A → set (R × C))
    --(evaluate: C → A → R → C → bool)

def iDSTR2iSTR (l : @iDESTR C A R) : @iSTR C A R :=
    ⟨
        singleton(l.initial),
        l.actions,
        λ c a, singleton(l.execute c a)
    ⟩

def iBDSTR2iSTR (l : @iBDSTR C A R) : @iSTR C A R :=
    ⟨
        singleton(l.initial),
        l.actions,
        λ c a, 
            match (l.execute c a) with 
            | none := ∅ 
            | some r := singleton(r)
            end
    ⟩

def synchronous_product {C₁ C₂ A₁ A₂ R₁ R₂ L₁ L₂ : Type}
    (lhs : @iSTR C₁ A₁ R₁)
    (eval₁ : L₁ → C₁ → A₁ → R₁ → C₁ → bool)
    (rhs : @iSTR C₂ A₂ R₂)
    (eval₂ : L₂ → C₂ → A₂ → R₂ → C₂ → bool)
    (mapping : set (L₁ × L₂))
: @iSTR (C₁×C₂) ((A₁ × A₂) × (R₁ × R₂) × (C₁ × C₂)) ( R₁ × R₂ ) :=
⟨
    { c | ∀ (c₁ ∈ lhs.initial) (c₂ ∈ rhs.initial), c = (c₁, c₂) },
    λ c, { a | 
            match c with
            | (c₁, c₂) := 
                ∀ (a₁ ∈ lhs.actions c₁) (a₂ ∈ rhs.actions c₂), 
                ∀ (rc₁ ∈ lhs.execute c₁ a₁) (rc₂ ∈ rhs.execute c₂ a₂), 
                ∃ m ∈ mapping,
                match rc₁, rc₂, m with 
                | (r₁, t₁), (r₂, t₂), (l₁, l₂) := 
                      eval₁ l₁ c₁ a₁ r₁ t₁ = tt 
                    ∧ eval₂ l₂ c₂ a₂ r₂ t₂ = tt 
                    → --------------------------------
                    a = ((a₁, a₂), (r₁, r₂), (c₁, c₂))
                end
            end    
        },
        λ c a, match a with | (_, rc) := singleton rc end
⟩ 



--For model-checking we need next stream with is_final
--High-level interface
class iExplicitNextStream :=
    (initial    : finset C)
    (next       : C → finset C)
    (is_final   : C → bool)


def iSTR2iExplicitNextStream
    (l : @iSTR C A R)                       -- the semantic transition relation
    (eval : C → bool)                       -- the configuration evaluation function, decide if a configuration is final
    [fic : finite l.initial]                -- a proof that the STR has finitely many initial states
    [fia : ∀ c, finite (l.actions c)]       -- a proof that for all configurations the STR has finitely many action
    [fie : ∀ c a, finite (l.execute c a)]   -- a proof that for all configuration and action the STR produces finitely many targets
: @iExplicitNextStream C :=
⟨ 
    (@finite.to_finset _ l.initial fic),
    λ c, (@finite.to_finset _ ({ x | ∀ a ∈ l.actions c, ∀ rc ∈ l.execute c a, x = (prod.snd rc)}) sorry),
    eval
⟩

-- a statefull scheduler, carry state over the choice operation
-- it has some arbitrary initial state
structure scheduler {S : Type} := 
    (initial : S)
    (choice : S → C → set A → (S × A)) 
    
def stateless_scheduler := @scheduler unit

def scheduling_filter { S : Type}
    (l : @iSTR C A R)
    (p : @scheduler C A S) 
: @iSTR (C × S) (S × A) R := 
⟨
    {cs | ∀ c ∈ l.initial, cs = (c, p.initial)}, --- .initial
    λ cs, singleton (p.choice (prod.snd cs) (prod.fst cs) (l.actions (prod.fst cs))), --.actions
    λ cs sa, 
        let 
             r := l.execute (prod.fst cs) (prod.snd sa) 
        in   
            {x | ∀ ec ∈ r, x = ((prod.fst ec), ((prod.snd ec), (prod.snd cs)))} --.execute
⟩

--stateless filtering policies 
structure filtering_policy := 
    (apply : C → set A → set A)
    (subset : ∀ c aSet,  apply c aSet ⊆ aSet)

def filter
    (l : @iSTR C A R)
    (filter : @filtering_policy C A)
: @iSTR C A R :=
⟨
    l.initial,
    λ c, filter.apply c (l.actions c),
    l.execute
⟩ 

def splitter -- named dispatcher previously 
    (actions : set A)
    (selector : A → bool)
: set A × set A := 
( 
    {a ∈ actions | selector a = tt}, 
    {a ∈ actions | selector a = ff} 
)

def merger(a₁ a₂ : set A) : set A := a₁ ∪ a₂

end gtr_cav