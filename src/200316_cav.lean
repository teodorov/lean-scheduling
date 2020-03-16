import data.set.finite data.stream

namespace gtr_cav

open set
--open byte

variables 
    {C : Type} -- configurations
    {A : Type} -- actions
    {E : Type} -- events
    {P : Type} -- atomic propositions

-- linear blocking semantic transition relation
structure iLSTR :=
    (initial : C)
    (actions : C → A)
    (execute : C → A → option (E × C))
    (one_action : ∀ c, ∃! a, actions c = a)
    (determinist_exe: ∀ c a, ∃! e t, execute c a = some (e, t))

inductive sos_exe  : @iLSTR C A E →  C → C → Prop
notation ⟨ l, ρ₀ ⟩ ` -x→ ` ρ₁ := sos_exe l ρ₀ ρ₁
| step : ∀ (l:@iLSTR C A E) e ρ₀ ρ₁, l.execute ρ₀ (l.actions ρ₀) = some (e, ρ₁)
        → -----------------------------
        ⟨ l, ρ₀ ⟩ -x→ ρ₁

-- deterministic execution semantic transition relation
structure iDESTR := 
    (initial : C)
    (actions : C → set A) 
    (execute : C → A → E × C)
    (determinist_exe : ∀ c a, ∃! e t, execute c a = (e, t))

-- blocking deterministic semantic transition relation
structure iBDSTR := 
    (initial : C)
    (actions : C → set A)
    (execute : C → A → option (E × C))

-- general semantic transition relation
structure iSTR :=
    (initial : set C)
    (actions : C → set A) 
    (execute : C → A → set (E × C))

def iDSTR2iSTR (l : @iDESTR C A E) : @iSTR C A E :=
    ⟨
        singleton(l.initial),
        l.actions,
        λ c a, singleton(l.execute c a)
    ⟩

def iBDSTR2iSTR (l : @iBDSTR C A E) : @iSTR C A E :=
    ⟨
        singleton(l.initial),
        l.actions,
        λ c a, 
            match (l.execute c a) with 
            | none := ∅ 
            | some r := singleton(r)
            end
    ⟩

def evaluator  := C → bool

--For model-checking we need next stream with is_final
--High-level interface
class iExplicitNextStream :=
    (initial    : finset C)
    (next       : C → finset C)
    (is_final   : C → bool)


def iSTR2iExplicitNextStream
    (l : @iSTR C A E)                       -- the semantic transition relation
    (eval : C → bool)                       -- the configuration evaluation function, decide if a configuration is final
    [fic : finite l.initial]                -- a proof that the STR has finitely many initial states
    [fia : ∀ c, finite (l.actions c)]       -- a proof that for all configurations the STR has finitely many action
    [fie : ∀ c a, finite (l.execute c a)]   -- a proof that for all configuration and action the STR produces finitely many targets
: @iExplicitNextStream C :=
⟨ 
    (@finite.to_finset _ l.initial fic),
    λ c, (@finite.to_finset _ ({ x | ∀ a ∈ l.actions c, ∀ ec ∈ l.execute c a, x = (prod.snd ec)}) sorry),
    eval
⟩

-- a statefull scheduler, carry state over the choice operation
-- it has some arbitrary initial state
structure scheduler {S : Type} := 
    (initial : S)
    (choice : S → C → set A → (S × A)) 
    
def stateless_scheduler := @scheduler unit

def scheduling_filter { S : Type}
    (l : @iSTR C A E)
    (p : @scheduler C A S) 
: @iSTR (C × S) (S × A) E := 
⟨
    {cs | ∀ c ∈ l.initial, cs = (c, p.initial)},
    λ cs, singleton (p.choice (prod.snd cs) (prod.fst cs) (l.actions (prod.fst cs))),
    λ cs sa, 
        let 
             r := l.execute (prod.fst cs) (prod.snd sa) 
        in   
            {x | ∀ ec ∈ r, x = ((prod.fst ec), ((prod.snd ec), (prod.snd cs)))}
⟩

--stateless filtering policies 
structure filtering_policy := 
    (apply : C → set A → set A)
    (subset : ∀ c aSet,  apply c aSet ⊆ aSet)

def filter
    (l : @iSTR C A E)
    (filter : @filtering_policy C A)
: @iSTR C A E :=
⟨
    l.initial,
    λ c, filter.apply c (l.actions c),
    l.execute
⟩ 

def splitter -- named dispatcher previously 
    (actions : set A)
    (selector : A → Prop)
: set A × set A := 
( 
    {a ∈ actions | selector a}, 
    {a ∈ actions | ¬selector a} 
)

def merger(a₁ a₂ : set A) : set A := a₁ ∪ a₂

end gtr_cav