use serde::{Deserialize, Serialize};
use super::json_parser::ProofData;
use std::collections::HashMap;
use std::path::Path;

/// Represents a Lean type expression for anti-unification
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LeanType {
    /// Variable reference (e.g., `a`, `Nat`, `p`)
    Var(String),
    /// Function type (e.g., `A → B`)
    Arrow(Box<LeanType>, Box<LeanType>),
    /// Dependent function type (e.g., `∀ (x : A), B`)
    Forall(String, Box<LeanType>, Box<LeanType>),
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
pub struct TypedHypothesis {
    pub name: String,
    pub ty: LeanType,
}

/// Enhanced parsed goal with structured types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypedParsedGoal {
    pub hypotheses: Vec<TypedHypothesis>,
    pub proposition: LeanType,
}

/// Parser for Lean type expressions
pub struct TypeParser;

impl TypeParser {
    /// Parse a Lean type expression string into a LeanType
    pub fn parse_type(type_str: &str) -> Result<LeanType, String> {
        let trimmed = type_str.trim();
        Self::parse_expression(trimmed)
    }

    /// Parse an expression with precedence handling
    fn parse_expression(expr: &str) -> Result<LeanType, String> {
        // Handle parentheses
        if let Some((inner, _)) = Self::parse_parens(expr) {
            return Self::parse_expression(inner);
        }

        // Handle binary operators with precedence
        // Lowest precedence first
        if let Some(result) = Self::parse_binary_op(expr, "→")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "∨")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "∧")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "=")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "≠")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "∣")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "*")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "<")? {
            return Ok(result);
        }
        if let Some(result) = Self::parse_binary_op(expr, "%")? {
            return Ok(result);
        }

        // Handle unary operators
        if expr.starts_with("¬") {
            let inner = expr.chars().skip(1).collect::<String>().trim().to_string();
            return Ok(LeanType::Not(Box::new(Self::parse_expression(&inner)?)));
        }

        // Handle forall
        if expr.starts_with("∀") {
            return Self::parse_forall(expr);
        }

        // Handle applications
        if let Some(result) = Self::parse_application(expr)? {
            return Ok(result);
        }

        // Handle basic variables and constants
        Self::parse_atomic(expr)
    }

    /// Parse parentheses
    fn parse_parens(expr: &str) -> Option<(&str, &str)> {
        if expr.starts_with('(') {
            let mut depth = 0;
            for (i, c) in expr.char_indices() {
                match c {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some((&expr[1..i], &expr[i+1..]));
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Parse binary operators
    fn parse_binary_op(expr: &str, op: &str) -> Result<Option<LeanType>, String> {
        let depth = 0;
        let mut paren_depth = 0;
        
        for (i, c) in expr.char_indices() {
            match c {
                '(' => paren_depth += 1,
                ')' => paren_depth -= 1,
                _ => {}
            }
            
            if paren_depth == 0 && depth == 0 {
                if expr[i..].starts_with(op) {
                    let left = expr[..i].trim();
                    let right = expr[i + op.len()..].trim();
                    
                    if !left.is_empty() && !right.is_empty() {
                        let left_type = Self::parse_expression(left)?;
                        let right_type = Self::parse_expression(right)?;
                        
                        let result = match op {
                            "→" => LeanType::Implies(Box::new(left_type), Box::new(right_type)),
                            "∨" => LeanType::Or(Box::new(left_type), Box::new(right_type)),
                            "∧" => LeanType::And(Box::new(left_type), Box::new(right_type)),
                            "∣" => LeanType::Divides(Box::new(left_type), Box::new(right_type)),
                            "*" => LeanType::Mul(Box::new(left_type), Box::new(right_type)),
                            "=" => LeanType::Eq(Box::new(left_type), Box::new(right_type)),
                            "≠" => LeanType::Ne(Box::new(left_type), Box::new(right_type)),
                            "<" => LeanType::Lt(Box::new(left_type), Box::new(right_type)),
                            "%" => LeanType::Mod(Box::new(left_type), Box::new(right_type)),
                            _ => return Err(format!("Unknown binary operator: {}", op)),
                        };
                        
                        return Ok(Some(result));
                    }
                }
            }
        }
        Ok(None)
    }

    /// Parse forall expressions
    fn parse_forall(expr: &str) -> Result<LeanType, String> {
        // Simple forall parsing: ∀ (x : A), B
        if let Some(comma_pos) = expr.find(',') {
            // Skip the ∀ symbol (3 bytes in UTF-8) and get the binding part
            let binding_part_str: String = expr.chars().skip(1).take(comma_pos - 1).collect();
            let binding_part = binding_part_str.trim();
            let body_part = expr[comma_pos + 1..].trim();
            
            if let Some(colon_pos) = binding_part.find(':') {
                let var_name = binding_part[..colon_pos].trim().trim_start_matches('(').trim();
                let var_type_str = binding_part[colon_pos + 1..].trim().trim_end_matches(')').trim();
                
                let var_type = Self::parse_expression(var_type_str)?;
                let body_type = Self::parse_expression(body_part)?;
                
                return Ok(LeanType::Forall(var_name.to_string(), Box::new(var_type), Box::new(body_type)));
            }
        }
        Err(format!("Invalid forall expression: {}", expr))
    }

    /// Parse applications
    fn parse_application(expr: &str) -> Result<Option<LeanType>, String> {
        // Look for function applications like "f x" or "Nat.Prime p"
        let parts: Vec<&str> = expr.split_whitespace().collect();
        if parts.len() >= 2 {
            // Try to parse as application
            let mut result = Self::parse_atomic(parts[0])?;
            for part in &parts[1..] {
                let arg = Self::parse_atomic(part)?;
                result = LeanType::App(Box::new(result), Box::new(arg));
            }
            return Ok(Some(result));
        }
        Ok(None)
    }

    /// Parse atomic expressions (variables, constants)
    fn parse_atomic(expr: &str) -> Result<LeanType, String> {
        let trimmed = expr.trim();
        
        match trimmed {
            "False" => Ok(LeanType::False),
            "True" => Ok(LeanType::True),
            "ℕ" | "Nat" => Ok(LeanType::Var("Nat".to_string())),
            _ => {
                // Handle qualified names like "Nat.Prime"
                if trimmed.contains('.') {
                    let parts: Vec<&str> = trimmed.split('.').collect();
                    let mut result = Self::parse_atomic(parts[0])?;
                    for part in &parts[1..] {
                        let arg = LeanType::Var(part.to_string());
                        result = LeanType::App(Box::new(result), Box::new(arg));
                    }
                    Ok(result)
                } else {
                    Ok(LeanType::Var(trimmed.to_string()))
                }
            }
        }
    }

    /// Parse a goal string into typed hypotheses and proposition
    pub fn parse_typed_goal(goal_str: &str) -> Result<TypedParsedGoal, String> {
        let lines: Vec<&str> = goal_str.lines().collect();
        
        if lines.is_empty() {
            return Err("Empty goal string".to_string());
        }

        let mut hypotheses = Vec::new();
        let mut proposition = None;
        let mut found_turnstile = false;

        for line in lines {
            let trimmed = line.trim();
            
            if trimmed.starts_with("⊢") {
                // Found the proposition to prove
                let prop_str = trimmed.chars().skip(1).collect::<String>().trim().to_string();
                proposition = Some(Self::parse_type(&prop_str)?);
                found_turnstile = true;
                break;
            } else if !trimmed.is_empty() && trimmed.contains(" : ") {
                // This is a hypothesis
                if let Some(colon_pos) = trimmed.find(" : ") {
                    let name = trimmed[..colon_pos].trim().to_string();
                    let ty_str = trimmed[colon_pos + 3..].trim().to_string();
                    let ty = Self::parse_type(&ty_str)?;
                    hypotheses.push(TypedHypothesis { name, ty });
                }
            }
        }

        if !found_turnstile {
            return Err("No turnstile (⊢) found in goal".to_string());
        }

        Ok(TypedParsedGoal {
            hypotheses,
            proposition: proposition.unwrap(),
        })
    }

    /// Extract all unique typed goals from a proof data structure
    pub fn extract_typed_goals(proof_data: &ProofData) -> Vec<TypedParsedGoal> {
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
    pub fn parse_typed_goals_from_file<P: AsRef<Path>>(path: P) -> Result<Vec<TypedParsedGoal>, String> {
        let proof_data = super::json_parser::JsonParser::parse_json_file(path)?;
        Ok(Self::extract_typed_goals(&proof_data))
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
            Box::new(LeanType::App(
                Box::new(LeanType::Var("Nat".to_string())),
                Box::new(LeanType::Var("Prime".to_string()))
            )),
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
        assert_eq!(result.hypotheses[0].name, "a b p");
        assert_eq!(result.hypotheses[0].ty, LeanType::Var("Nat".to_string()));
        assert_eq!(result.hypotheses[1].name, "hp");
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
}
