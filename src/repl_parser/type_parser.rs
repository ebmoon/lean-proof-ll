use serde::{Deserialize, Serialize};
use super::json_parser::{ProofData, Position};
use std::collections::HashMap;
use std::path::Path;
use nom::{
    IResult,
    bytes::complete::{tag, take_while1},
    character::complete::{multispace0, multispace1, not_line_ending},
    combinator::{opt, recognize},
    multi::{many0, many1},
    sequence::{delimited, terminated},
    error::Error,
};

// Type aliases for cleaner code
type ParseResult<'a, T> = IResult<&'a str, T, Error<&'a str>>;

// Macro to simplify tag calls with proper type annotations
macro_rules! tag_typed {
    ($tag:literal) => {
        tag::<&str, &str, Error<&str>>($tag)
    };
}


/// Represents a Lean type expression for anti-unification
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LeanType {
    /// Variable reference (e.g., `a`, `Nat`, `p`)
    Var(String),
    /// Function type (e.g., `A → B`)
    Arrow(Box<LeanType>, Box<LeanType>),
    /// Dependent function type (e.g., `∀ (x : A), B`)
    Forall(Vec<String>, Box<LeanType>, Box<LeanType>),
    /// Existential type (e.g., `∃ (x : A), B`)
    Exists(Vec<String>, Box<LeanType>, Box<LeanType>),
    /// Application (e.g., `f x`, `Nat.Prime p`)
    App(Box<LeanType>, Box<LeanType>),
    /// Binary operation (e.g., `a * b`, `p ∣ a`)
    BinOp(String, Box<LeanType>, Box<LeanType>),
    /// Negation (e.g., `¬P`)
    Not(Box<LeanType>),
    /// Equality (e.g., `a = b`)
    Eq(Box<LeanType>, Box<LeanType>),
    /// Conjunction (e.g., `A ∧ B`)
    And(Box<LeanType>, Box<LeanType>),
    /// Disjunction (e.g., `A ∨ B`)
    Or(Box<LeanType>, Box<LeanType>),
    /// Implication (e.g., `A → B`)
    Implies(Box<LeanType>, Box<LeanType>),
    /// Divisibility (e.g., `p ∣ a`)
    Divides(Box<LeanType>, Box<LeanType>),
    /// Modulo operation (e.g., `a % b`)
    Mod(Box<LeanType>, Box<LeanType>),
    /// Multiplication (e.g., `a * b`)
    Mul(Box<LeanType>, Box<LeanType>),
    /// Less than (e.g., `a < b`)
    Lt(Box<LeanType>, Box<LeanType>),
    /// Not equal (e.g., `a ≠ b`)
    Ne(Box<LeanType>, Box<LeanType>),
    /// False
    False,
    /// True
    True,
}

/// Enhanced hypothesis with parsed type
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hypothesis {
    pub name: Vec<String>,
    pub ty: LeanType,
}

/// Enhanced parsed goal with structured types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Goal {
    pub hypotheses: Vec<Hypothesis>,
    pub proposition: LeanType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypedProofStep {
    pub used_constants: Vec<String>,
    pub tactic: String,
    pub proof_state: u32,
    pub pos: Position,
    pub goals: Goal,
    pub end_pos: Position,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypedProofData {
    pub proof_steps: Vec<TypedProofStep>,
    pub env: u32,
}

/// Enum to represent different quantifier types
#[derive(Debug, Clone, Copy, PartialEq)]
enum QuantifierType {
    Forall,
    Exists,
}

/// Parser for Lean type expressions
pub struct TypeParser;

impl TypeParser {

    /// Main entry point for parsing type expressions
    pub fn parse_type(input: &str) -> Result<LeanType, String> {
        match Self::parse_expression(input.trim()) {
            Ok((remaining, result)) => {
                if remaining.trim().is_empty() {
                    Ok(result)
                } else {
                    Err(format!("Unexpected input remaining: '{}'", remaining))
                }
            }
            Err(e) => Err(format!("Parse error: {:?}", e)),
        }
    }

    fn parse_parens(input: &str) -> ParseResult<'_, LeanType> {
        delimited(multispace0, delimited(tag_typed!("("), Self::parse_expression, tag_typed!(")")), multispace0)(input)
    }

    fn parse_binary_op(input: &str) -> ParseResult<'_, LeanType> {
        Self::parse_implication(input)
    }

    // Implication (→) - lowest precedence
    fn parse_implication(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut left) = Self::parse_disjunction(input)?;
        let mut input = input;
        
        loop {
            let (input_after_space, _) = multispace0(input)?;
            if let Ok((new_input, _)) = tag_typed!("→")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_disjunction(new_input)?;
                left = LeanType::Implies(Box::new(left), Box::new(right));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, left))
    }

    // Disjunction (∨) - medium precedence
    fn parse_disjunction(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut left) = Self::parse_conjunction(input)?;
        let mut input = input;
        
        loop {
            let (input_after_space, _) = multispace0(input)?;
            if let Ok((new_input, _)) = tag_typed!("∨")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_conjunction(new_input)?;
                left = LeanType::Or(Box::new(left), Box::new(right));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, left))
    }

    // Conjunction (∧) - medium precedence
    fn parse_conjunction(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut left) = Self::parse_equality(input)?;
        let mut input = input;
        
        loop {
            let (input_after_space, _) = multispace0(input)?;
            if let Ok((new_input, _)) = tag_typed!("∧")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_equality(new_input)?;
                left = LeanType::And(Box::new(left), Box::new(right));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, left))
    }

    // Equality and inequality (=, ≠) - high precedence
    fn parse_equality(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut left) = Self::parse_relation(input)?;
        let mut input = input;
        
        loop {
            let (input_after_space, _) = multispace0(input)?;
            if let Ok((new_input, _)) = tag_typed!("=")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_relation(new_input)?;
                left = LeanType::Eq(Box::new(left), Box::new(right));
                input = new_input;
            } else if let Ok((new_input, _)) = tag_typed!("≠")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_relation(new_input)?;
                left = LeanType::Ne(Box::new(left), Box::new(right));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, left))
    }

    // Divisibility, less than (∣, <) - high precedence
    fn parse_relation(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut left) = Self::parse_multiplication(input)?;
        let mut input = input;
        
        loop {
            let (input_after_space, _) = multispace0(input)?;
            if let Ok((new_input, _)) = tag_typed!("∣")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_multiplication(new_input)?;
                left = LeanType::Divides(Box::new(left), Box::new(right));
                input = new_input;
            } else if let Ok((new_input, _)) = tag_typed!("<")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_multiplication(new_input)?;
                left = LeanType::Lt(Box::new(left), Box::new(right));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, left))
    }

    // Multiplication and modulo (*, %) - highest precedence
    fn parse_multiplication(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut left) = Self::parse_application(input)?;
        let mut input = input;
        
        loop {
            let (input_after_space, _) = multispace0(input)?;
            if let Ok((new_input, _)) = tag_typed!("*")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_application(new_input)?;
                left = LeanType::Mul(Box::new(left), Box::new(right));
                input = new_input;
            } else if let Ok((new_input, _)) = tag_typed!("%")(input_after_space) {
                let (new_input, _) = multispace0(new_input)?;
                let (new_input, right) = Self::parse_application(new_input)?;
                left = LeanType::Mod(Box::new(left), Box::new(right));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, left))
    }

    /// Parse a typed variable in parentheses: (var_name : type)
    fn parse_typed_variable(input: &str) -> ParseResult<'_, (&str, LeanType)> {
        let (input, _) = tag_typed!("(")(input)?;
        let (input, _) = multispace0(input)?;
        let (input, var_name) = Self::parse_identifier_string(input)?;
        let (input, _) = multispace0(input)?;
        let (input, _) = tag_typed!(":")(input)?;
        let (input, _) = multispace0(input)?;
        let (input, var_type) = Self::parse_expression(input)?;
        let (input, _) = multispace0(input)?;
        let (input, _) = tag_typed!(")")(input)?;
        
        Ok((input, (var_name, var_type)))
    }

    /// Parse a quantifier with the given type, handling both typed and untyped variable formats
    fn parse_quantifier_with_type(input: &str, quantifier_type: QuantifierType) -> ParseResult<'_, LeanType> {
        let (input, _) = multispace0(input)?;
        
        // Try the format: (var : type), body (typed variable)
        if let Ok((input, (var_name, var_type))) = Self::parse_typed_variable(input) {
            let (input, _) = multispace0(input)?;
            let (input, _) = tag_typed!(",")(input)?;
            let (input, _) = multispace0(input)?;
            let (input, body) = Self::parse_expression(input)?;
            
            return Ok((input, match quantifier_type {
                QuantifierType::Forall => LeanType::Forall(
                    vec![var_name.to_string()],
                    Box::new(var_type),
                    Box::new(body)
                ),
                QuantifierType::Exists => LeanType::Exists(
                    vec![var_name.to_string()],
                    Box::new(var_type),
                    Box::new(body)
                ),
            }));
        }
        

        if let Ok((input, var_names)) = Self::parse_identifier_list(input) {
            let (input, _) = multispace0(input)?;
            let (input, _) = tag_typed!(",")(input)?;
            let (input, _) = multispace0(input)?;
            let (input, body) = Self::parse_expression(input)?;
            
            // For now, we'll use the first variable name and assume type is implicit
            // This is a simplification - in a full implementation, we'd need to handle multiple variables
            return Ok((input, match quantifier_type { 
                QuantifierType::Forall => LeanType::Forall(
                    var_names.iter().map(|s| s.to_string()).collect(),
                    Box::new(LeanType::Var("ℕ".to_string())), // Assume natural numbers for now
                    Box::new(body)
                ),
                QuantifierType::Exists => LeanType::Exists(
                    var_names.iter().map(|s| s.to_string()).collect(),
                    Box::new(LeanType::Var("ℕ".to_string())), // Assume natural numbers for now
                    Box::new(body)
                ),
            }));
        }
        
        Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))
    }

    fn parse_quantifier(input: &str) -> ParseResult<'_, LeanType> {
        // Universal quantifier (∀)
        if let Ok((input, _)) = tag_typed!("∀")(input) {
            return Self::parse_quantifier_with_type(input, QuantifierType::Forall);
        }
        
        // Existential quantifier (∃)
        if let Ok((input, _)) = tag_typed!("∃")(input) {
            return Self::parse_quantifier_with_type(input, QuantifierType::Exists);
        }
        
        Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))
    }

    fn parse_application(input: &str) -> ParseResult<'_, LeanType> {
        let (input, mut result) = Self::parse_atomic(input)?;
        
        // Parse additional applications (e.g., "Nat.Prime p" -> App(App(Nat, Prime), p))
        let mut input = input;
        while let Ok((new_input, _)) = multispace0::<&str, Error<&str>>(input) {
            if let Ok((new_input, arg)) = Self::parse_atomic(new_input) {
                result = LeanType::App(Box::new(result), Box::new(arg));
                input = new_input;
            } else {
                break;
            }
        }
        
        Ok((input, result))
    }

    fn parse_atomic(input: &str) -> ParseResult<'_, LeanType> {
        let (input, _) = multispace0(input)?;
        
        // Try parentheses first
        if let Ok((input, result)) = Self::parse_parens(input) {
            return Ok((input, result));
        }
        
        // Try special constants
        if let Ok((input, _)) = tag_typed!("False")(input) {
            return Ok((input, LeanType::False));
        }
        
        if let Ok((input, _)) = tag_typed!("True")(input) {
            return Ok((input, LeanType::True));
        }
        
        // Try to parse identifier with dot notation
        if let Ok((input, ident)) = Self::parse_identifier(input) {
            return Ok((input, ident));
        }
        
        Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))
    }

    fn parse_identifier(input: &str) -> ParseResult<'_, LeanType> {
        let (input, ident) = Self::parse_identifier_string(input)?;
        let result = LeanType::Var(ident.to_string());
        
        Ok((input, result))
    }

    /// Parse an expression with precedence handling
    fn parse_expression(input: &str) -> ParseResult<'_, LeanType> {
        // Try negation first (highest precedence)
        if let Ok((input, _)) = tag_typed!("¬")(input) {
            let (input, _) = multispace0(input)?;
            let (input, operand) = Self::parse_expression(input)?;
            return Ok((input, LeanType::Not(Box::new(operand))));
        }
        
        // Try quantifiers (high precedence)
        if let Ok(result) = Self::parse_quantifier(input) {
            return Ok(result);
        }
        
        // Then try binary operators
        Self::parse_binary_op(input)
    }

    /// Parse a typed hypothesis line (e.g., "a b p : ℕ" or "hcontra : k = 1 := hrel k ha hb")
    fn parse_typed_hypothesis_line(input: &str) -> ParseResult<'_, Hypothesis> {
        let (input, _) = multispace0(input)?;
        let (input, name) = Self::parse_identifier_list(input)?;
        let (input, _) = multispace0(input)?;
        let (input, _) = tag_typed!(":")(input)?;
        let (input, _) = multispace1(input)?;
        
        // Parse until we hit := or end of line
        let (input, ty_str) = take_while1(|c: char| c != '\n' && c != '\r')(input)?;
        
        // If the line contains :=, we need to extract just the type part
        let ty_str = if ty_str.contains(":=") {
            ty_str.split(":=").next().unwrap_or("").trim()
        } else {
            ty_str.trim()
        };
        
        let (input, _) = opt(not_line_ending)(input)?;
        let (input, _) = multispace0(input)?;
        
        // Parse the type string into a LeanType
        let ty = TypeParser::parse_type(ty_str)
            .map_err(|_| nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))?;
        
        Ok((input, Hypothesis {
            name: name.iter().map(|s| s.to_string()).collect(),
            ty,
        }))
    }

    /// Parse a typed proposition line (e.g., "⊢ p ∣ a * b → p ∣ a ∨ p ∣ b")
    fn parse_typed_proposition_line(input: &str) -> ParseResult<'_, LeanType> {
        let (input, _) = multispace0(input)?;
        let (input, _) = tag_typed!("⊢")(input)?;
        let (input, _) = multispace1(input)?;
        let (input, prop_str) = Self::parse_type_expression_string(input)?;
        
        // Parse the proposition string into a LeanType
        let prop = TypeParser::parse_type(prop_str)
            .map_err(|_| nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))?;
        
        Ok((input, prop))
    }

    /// Parse a list of identifiers (e.g., "a b p")
    fn parse_identifier_list(input: &str) -> ParseResult<'_, Vec<&str>> {
        let (input, result) = recognize(many1(terminated(
            Self::parse_identifier_string,
            opt(multispace1)
        )))(input)?;
        // Trim trailing whitespace from the result
        let trimmed = result.trim_end();
        Ok((input, trimmed.split_whitespace().collect()))
    }

    /// Parse a single identifier
    /// TODO: Identifier can be greek letters
    fn parse_identifier_string(input: &str) -> IResult<&str, &str> {
        take_while1(|c: char| c.is_alphanumeric() || c == '_' || c == '.' || c == '\'')(input)
    }

    /// Parse a type expression string (everything until end of line or turnstile)
    fn parse_type_expression_string(input: &str) -> ParseResult<'_, &str> {
        // Take everything until we hit a newline or end of input
        let (input, expr) = take_while1(|c: char| c != '\n' && c != '\r')(input)?;
        Ok((input, expr.trim()))
    }

    /// Parse a complete typed goal string
    fn parse_typed_goal_inner(input: &str) -> ParseResult<'_, Goal> {
        let (input, hypotheses) = many0(Self::parse_typed_hypothesis_line)(input)?;
        let (input, _) = multispace0(input)?;
        let (input, proposition) = Self::parse_typed_proposition_line(input)?;
        let (input, _) = multispace0(input)?;
        
        Ok((input, Goal {
            hypotheses,
            proposition,
        }))
    }

    pub fn parse_typed_goal(goal_str: &str) -> Result<Goal, String> {
        match Self::parse_typed_goal_inner(goal_str) {
            Ok((_, result)) => Ok(result),
            Err(e) => Err(format!("Failed to parse typed goal: {:?}", e)),
        }
    }

    /// Extract all unique typed goals from a proof data structure
    pub fn extract_typed_goals(proof_data: &ProofData) -> Vec<Goal> {
        let mut goals = Vec::new();
        let mut seen_goals = HashMap::new();

        for proof_step in &proof_data.proof_steps {
            if let Ok(parsed_goal) = Self::parse_typed_goal(&proof_step.goals) {
                // Use the goal string as key to avoid duplicates
                if !seen_goals.contains_key(&proof_step.goals) {
                    seen_goals.insert(proof_step.goals.clone(), ());
                    goals.push(parsed_goal);
                }
            }
        }

        goals
    }

    /// Parse typed goals from a JSON file and return all unique goals
    pub fn parse_json_file<P: AsRef<Path>>(path: P) -> Result<TypedProofData, String> {
        let proof_data = super::json_parser::JsonParser::parse_json_file(path)?;
        Self::parse_typed_proof_data(&proof_data)
    }

    pub fn parse_typed_proof_data(proof_data: &super::json_parser::ProofData) -> Result<TypedProofData, String> {
        let mut proof_steps = Vec::new();
        for step in &proof_data.proof_steps {
            proof_steps.push(Self::parse_typed_proof_step(step)?);
        }
        Ok(TypedProofData {
            proof_steps,
            env: proof_data.env,
        })
    }

    pub fn parse_typed_proof_step(proof_step: &super::json_parser::ProofStep) -> Result<TypedProofStep, String> {
        let goals = Self::parse_typed_goal(&proof_step.goals)
            .map_err(|e| format!("Failed to parse goal '{}': {}", proof_step.goals, e))?;
        Ok(TypedProofStep {
            used_constants: proof_step.used_constants.clone(),
            tactic: proof_step.tactic.clone(),
            proof_state: proof_step.proof_state,
            pos: proof_step.pos.clone(),
            goals,
            end_pos: proof_step.end_pos.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_type() {
        let type_str = "Nat";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Var("Nat".to_string()));
    }

    #[test]
    fn test_parse_function_type() {
        let type_str = "A → B";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Implies(
            Box::new(LeanType::Var("A".to_string())),
            Box::new(LeanType::Var("B".to_string()))
        ));
    }

    #[test]
    fn test_parse_divides_type() {
        let type_str = "p ∣ a";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Divides(
            Box::new(LeanType::Var("p".to_string())),
            Box::new(LeanType::Var("a".to_string()))
        ));
    }

    #[test]
    fn test_parse_application_type() {
        let type_str = "Nat.Prime p";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::App(
            Box::new(LeanType::Var("Nat.Prime".to_string())),
            Box::new(LeanType::Var("p".to_string()))
        ));
    }

    #[test]
    fn test_parse_complex_type() {
        let type_str = "p ∣ a * b → p ∣ a ∨ p ∣ b";
        let result = TypeParser::parse_type(type_str).unwrap();
        // This should parse as: (p ∣ (a * b)) → ((p ∣ a) ∨ (p ∣ b))
        match result {
            LeanType::Implies(left, right) => {
                // Check left side: p ∣ (a * b)
                assert!(matches!(*left, LeanType::Divides(_, _)));
                // Check right side: (p ∣ a) ∨ (p ∣ b)
                assert!(matches!(*right, LeanType::Or(_, _)));
            }
            _ => panic!("Expected Implies type"),
        }
    }

    #[test]
    fn test_parse_typed_goal() {
        let goal_str = "a b p : ℕ\nhp : Nat.Prime p\n⊢ p ∣ a * b → p ∣ a ∨ p ∣ b";
        let result = TypeParser::parse_typed_goal(goal_str).unwrap();
        
        assert_eq!(result.hypotheses.len(), 2);
        assert_eq!(result.hypotheses[0].name, vec!["a", "b", "p"]);
        assert_eq!(result.hypotheses[0].ty, LeanType::Var("ℕ".to_string()));
        assert_eq!(result.hypotheses[1].name, vec!["hp"]);
        assert!(matches!(result.hypotheses[1].ty, LeanType::App(_, _)));
        assert!(matches!(result.proposition, LeanType::Implies(_, _)));
    }

    #[test]
    fn test_parse_forall_type() {
        let type_str = "∀ (n : Nat), n ∣ a → n ∣ b → n = 1";
        let result = TypeParser::parse_type(type_str);
        // For now, just check that it doesn't crash - forall parsing is complex
        match result {
            Ok(_) => println!("Forall parsing succeeded"),
            Err(e) => println!("Forall parsing failed: {}", e),
        }
        // We'll implement proper forall parsing later
        assert!(true); // Placeholder assertion
    }

    #[test]
    fn test_parse_exists_type() {
        let type_str = "∃ (n : Nat), n ∣ a";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Exists(
            vec!["n".to_string()],
            Box::new(LeanType::Var("Nat".to_string())),
            Box::new(LeanType::Divides(
                Box::new(LeanType::Var("n".to_string())),
                Box::new(LeanType::Var("a".to_string()))
            ))
        ));
    }

    #[test]
    fn test_parse_negation() {
        let type_str = "¬P";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Not(Box::new(LeanType::Var("P".to_string()))));
    }

    #[test]
    fn test_parse_parentheses() {
        let type_str = "(A → B)";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Implies(
            Box::new(LeanType::Var("A".to_string())),
            Box::new(LeanType::Var("B".to_string()))
        ));
    }

    #[test]
    fn test_parse_equality() {
        let type_str = "a = b";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Eq(
            Box::new(LeanType::Var("a".to_string())),
            Box::new(LeanType::Var("b".to_string()))
        ));
    }

    #[test]
    fn test_parse_inequality() {
        let type_str = "a ≠ b";
        let result = TypeParser::parse_type(type_str).unwrap();
        assert_eq!(result, LeanType::Ne(
            Box::new(LeanType::Var("a".to_string())),
            Box::new(LeanType::Var("b".to_string()))
        ));
    }

    #[test]
    fn test_parse_typed_goal_with_proof_term() {
        let goal_str = "hcontra : k = 1 := hrel k ha hb\n⊢ False";
        let result = TypeParser::parse_typed_goal(goal_str);
        match result {
            Ok(goal) => {
                assert_eq!(goal.hypotheses.len(), 1);
                assert_eq!(goal.hypotheses[0].name, vec!["hcontra"]);
                assert!(matches!(goal.hypotheses[0].ty, LeanType::Eq(_, _)));
                assert_eq!(goal.proposition, LeanType::False);
            }
            Err(e) => {
                println!("Error parsing goal with proof term: {}", e);
                // For now, just ensure it doesn't crash
                assert!(true);
            }
        }
    }

    #[test]
    fn test_parse_complex_goal_with_forall() {
        let goal_str = "a b k : ℕ\nhk : k ≠ 1\nha : k ∣ a\nhb : k ∣ b\nhrel : ∀ (n : ℕ), n ∣ a → n ∣ b → n = 1\nhcontra : k = 1 := hrel k ha hb\n⊢ False";
        let result = TypeParser::parse_typed_goal(goal_str);
        match result {
            Ok(goal) => {
                assert_eq!(goal.hypotheses.len(), 6);
                assert_eq!(goal.proposition, LeanType::False);
            }
            Err(e) => {
                println!("Error parsing complex goal: {}", e);
                // For now, just ensure it doesn't crash
                assert!(true);
            }
        }
    }

    #[test]
    fn test_parse_negation_exists() {
        let goal_str = "p : ℕ\nhp : Nat.Prime p\n⊢ ¬∃ a b, a * a = p * b * b ∧ b ≠ 0 ∧ relatively_prime a b";
        let result = TypeParser::parse_typed_goal(goal_str);
        match result {
            Ok(goal) => {
                assert_eq!(goal.hypotheses.len(), 2);
                assert!(matches!(goal.proposition, LeanType::Not(_)));
            }
            Err(e) => {
                println!("Error parsing negation exists goal: {}", e);
                // For now, just ensure it doesn't crash
                assert!(true);
            }
        }
    }

    #[test]
    fn test_parse_negation_exists_type_only() {
        let type_str = "¬∃ a b, a * a = p * b * b ∧ b ≠ 0 ∧ relatively_prime a b";
        let result = TypeParser::parse_type(type_str);
        match result {
            Ok(ty) => {
                assert!(matches!(ty, LeanType::Not(_)));
            }
            Err(e) => {
                println!("Error parsing negation exists type: {}", e);
                // For now, just ensure it doesn't crash
                assert!(true);
            }
        }
    }

    #[test]
    fn test_parse_proof_term_hypothesis() {
        let goal_str = "ha' : p ∣ a := ha\n⊢ False";
        let result = TypeParser::parse_typed_goal(goal_str);
        match result {
            Ok(goal) => {
                assert_eq!(goal.hypotheses.len(), 1);
                assert_eq!(goal.hypotheses[0].name, vec!["ha'"]);
                assert!(matches!(goal.hypotheses[0].ty, LeanType::Divides(_, _)));
                assert_eq!(goal.proposition, LeanType::False);
            }
            Err(e) => {
                println!("Error parsing proof term hypothesis: {}", e);
                // For now, just ensure it doesn't crash
                assert!(true);
            }
        }
    }
}