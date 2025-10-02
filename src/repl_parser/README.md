# Lean Proof Goal Parser

A Rust module for parsing Lean proof goals from JSON files into structured hypotheses and propositions, with support for anti-unification through typed parsing.

## Features

- Parse individual goal strings into hypotheses and propositions
- Parse complete JSON files containing proof tactics and goals
- Extract unique goals from proof data
- Handle Lean's turnstile symbol (⊢) correctly
- Support for complex hypothesis types and propositions
- **NEW**: Parse Lean dependent types into structured representations for anti-unification
- Support for function types, applications, binary operations, and more

## Usage

### Basic Usage

```rust
use lean_proof_ll::goal_parser::{GoalParser, TypeParser, LeanType};

// Parse a single goal string (string format)
let goal_str = "a b p : ℕ\nhp : Nat.Prime p\n⊢ p ∣ a * b → p ∣ a ∨ p ∣ b";
let parsed_goal = GoalParser::parse_goal(goal_str)?;

// Parse goals from a JSON file (string format)
let goals = GoalParser::parse_goals_from_file("examples/prime_subgoals.json")?;

// Parse a single goal string with typed parsing (for anti-unification)
let typed_goal = GoalParser::parse_typed_goal(goal_str)?;

// Parse goals from a JSON file with typed parsing
let typed_goals = GoalParser::parse_typed_goals_from_file("examples/prime_subgoals.json")?;

// Parse individual types
let type_expr = TypeParser::parse_type("p ∣ a * b → p ∣ a ∨ p ∣ b")?;
```

### Command Line Usage

```bash
# Parse goals from a JSON file (string format)
cargo run examples/prime_subgoals.json

# Parse goals with typed parsing (for anti-unification)
cargo run examples/prime_subgoals.json --typed

# Parse goals from another JSON file
cargo run examples/two_subgoals.json --typed
```

## Data Structures

### ParsedGoal
Represents a parsed goal with:
- `hypotheses`: Vector of hypothesis names and their types (string format)
- `proposition`: The proposition to prove (after the ⊢ symbol, string format)

### Hypothesis
Represents a single hypothesis with:
- `name`: The hypothesis name(s)
- `ty`: The type of the hypothesis (string format)

### TypedParsedGoal
Represents a parsed goal with structured types for anti-unification:
- `hypotheses`: Vector of typed hypotheses
- `proposition`: The proposition to prove as a structured type

### TypedHypothesis
Represents a single hypothesis with structured type:
- `name`: The hypothesis name(s)
- `ty`: The type as a LeanType enum

### LeanType
Enum representing Lean type expressions for anti-unification:
- `Var(String)`: Variable reference (e.g., `a`, `Nat`, `p`)
- `Arrow(Box<LeanType>, Box<LeanType>)`: Function type (e.g., `A → B`)
- `Forall(String, Box<LeanType>, Box<LeanType>)`: Dependent function type (e.g., `∀ (x : A), B`)
- `App(Box<LeanType>, Box<LeanType>)`: Application (e.g., `f x`, `Nat.Prime p`)
- `Divides(Box<LeanType>, Box<LeanType>)`: Divisibility (e.g., `p ∣ a`)
- `Mul(Box<LeanType>, Box<LeanType>)`: Multiplication (e.g., `a * b`)
- `Eq(Box<LeanType>, Box<LeanType>)`: Equality (e.g., `a = b`)
- `Or(Box<LeanType>, Box<LeanType>)`: Disjunction (e.g., `A ∨ B`)
- `And(Box<LeanType>, Box<LeanType>)`: Conjunction (e.g., `A ∧ B`)
- `Implies(Box<LeanType>, Box<LeanType>)`: Implication (e.g., `A → B`)
- `Not(Box<LeanType>)`: Negation (e.g., `¬P`)
- `Mod(Box<LeanType>, Box<LeanType>)`: Modulo operation (e.g., `a % b`)
- `Lt(Box<LeanType>, Box<LeanType>)`: Less than (e.g., `a < b`)
- `Ne(Box<LeanType>, Box<LeanType>)`: Not equal (e.g., `a ≠ b`)
- `False`: False constant
- `True`: True constant

## JSON Format

The parser expects JSON files with the following structure:

```json
{
  "tactics": [
    {
      "usedConstants": ["Dvd.dvd", "HMul.hMul", ...],
      "tactic": "intro h",
      "proofState": 0,
      "pos": {"line": 7, "column": 2},
      "goals": "a b p : ℕ\nhp : Nat.Prime p\n⊢ p ∣ a * b → p ∣ a ∨ p ∣ b",
      "endPos": {"line": 7, "column": 9}
    }
  ],
  "env": 0
}
```

## Goal Format

Goals are expected to be in Lean format:

```
hypothesis1 : Type1
hypothesis2 : Type2
⊢ proposition_to_prove
```

## Examples

The `examples/` directory contains sample JSON files:
- `prime_subgoals.json`: Contains 39 unique goals from prime number proofs
- `two_subgoals.json`: Contains 31 unique goals from proofs involving the number 2

## Testing

Run the tests with:

```bash
cargo test
```

## Dependencies

- `serde`: For JSON serialization/deserialization
- `serde_json`: For JSON parsing

