use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;
use nom::{
    IResult,
    bytes::complete::{tag, take_while1},
    character::complete::{multispace0, multispace1, not_line_ending},
    combinator::{opt, recognize},
    multi::{many0, many1},
    sequence::{terminated},
};

/// Represents a hypothesis in a Lean goal
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hypothesis {
    pub name: String,
    pub ty: String,
}

/// Represents a parsed goal with hypotheses and proposition to prove
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParsedGoal {
    pub hypotheses: Vec<Hypothesis>,
    pub proposition: String,
}

/// Represents a single ProofStep from the JSON file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStep {
    #[serde(rename = "usedConstants")]
    pub used_constants: Vec<String>,
    pub tactic: String,
    #[serde(rename = "proofState")]
    pub proof_state: u32,
    pub pos: Position,
    pub goals: String,
    #[serde(rename = "endPos")]
    pub end_pos: Position,
}

/// Represents a position in the source code
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Position {
    pub line: u32,
    pub column: u32,
}

/// Represents the complete JSON structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofData {
    #[serde(rename = "tactics")]
    pub proof_steps: Vec<ProofStep>,
    pub env: u32,
}

/// Parser for Lean goals from JSON files
pub struct JsonParser;

impl JsonParser {
    /// Parse a goal string into hypotheses and proposition using nom
    /// 
    /// The goal format is typically:
    /// hypothesis1 : Type1
    /// hypothesis2 : Type2
    /// ⊢ proposition_to_prove
    pub fn parse_goal(goal_str: &str) -> Result<ParsedGoal, String> {
        match parse_goal_complete(goal_str) {
            Ok((_, result)) => Ok(result),
            Err(e) => Err(format!("Failed to parse goal: {:?}", e)),
        }
    }

    /// Parse a JSON file containing proof data
    pub fn parse_json_file<P: AsRef<Path>>(path: P) -> Result<ProofData, String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read file: {}", e))?;
        
        serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse JSON: {}", e))
    }
}

// Nom parser combinators for goal parsing

/// Parse a complete goal string
fn parse_goal_complete(input: &str) -> IResult<&str, ParsedGoal> {
    let (input, hypotheses) = many0(parse_hypothesis_line)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, proposition) = parse_proposition_line(input)?;
    let (input, _) = multispace0(input)?;
    
    Ok((input, ParsedGoal {
        hypotheses,
        proposition: proposition.to_string(),
    }))
}

/// Parse a hypothesis line (e.g., "a b p : ℕ")
fn parse_hypothesis_line(input: &str) -> IResult<&str, Hypothesis> {
    let (input, _) = multispace0(input)?;
    let (input, name) = parse_identifier_list(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(":")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, ty) = parse_type_expression(input)?;
    let (input, _) = opt(not_line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    
    Ok((input, Hypothesis {
        name: name.to_string(),
        ty: ty.to_string(),
    }))
}

/// Parse a proposition line (e.g., "⊢ p ∣ a * b → p ∣ a ∨ p ∣ b")
fn parse_proposition_line(input: &str) -> IResult<&str, &str> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("⊢")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, proposition) = parse_type_expression(input)?;
    
    Ok((input, proposition))
}

/// Parse a list of identifiers (e.g., "a b p")
fn parse_identifier_list(input: &str) -> IResult<&str, &str> {
    let (input, result) = recognize(many1(terminated(
        parse_identifier,
        opt(multispace1)
    )))(input)?;
    // Trim trailing whitespace from the result
    let trimmed = result.trim_end();
    Ok((input, trimmed))
}

/// Parse a single identifier
fn parse_identifier(input: &str) -> IResult<&str, &str> {
    take_while1(|c: char| c.is_alphanumeric() || c == '_' || c == '.')(input)
}

/// Parse a type expression (everything until end of line or turnstile)
fn parse_type_expression(input: &str) -> IResult<&str, &str> {
    // Take everything until we hit a newline or end of input
    // This is a simplified version - in a real implementation you might want
    // more sophisticated type parsing
    let (input, expr) = take_while1(|c: char| c != '\n' && c != '\r')(input)?;
    Ok((input, expr.trim()))
}