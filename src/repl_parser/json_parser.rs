use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

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
    /// Parse a goal string into hypotheses and proposition
    /// 
    /// The goal format is typically:
    /// hypothesis1 : Type1
    /// hypothesis2 : Type2
    /// ⊢ proposition_to_prove
    pub fn parse_goal(goal_str: &str) -> Result<ParsedGoal, String> {
        let lines: Vec<&str> = goal_str.lines().collect();
        
        if lines.is_empty() {
            return Err("Empty goal string".to_string());
        }

        let mut hypotheses = Vec::new();
        let mut proposition = String::new();
        let mut found_turnstile = false;

        for line in lines {
            let trimmed = line.trim();
            
            if trimmed.starts_with("⊢") {
                // Found the proposition to prove
                // Skip the turnstile symbol (3 bytes in UTF-8)
                proposition = trimmed.chars().skip(1).collect::<String>().trim().to_string();
                found_turnstile = true;
                break;
            } else if !trimmed.is_empty() && trimmed.contains(" : ") {
                // This is a hypothesis
                if let Some(colon_pos) = trimmed.find(" : ") {
                    let name = trimmed[..colon_pos].trim().to_string();
                    let ty = trimmed[colon_pos + 3..].trim().to_string();
                    hypotheses.push(Hypothesis { name, ty });
                }
            }
        }

        if !found_turnstile {
            return Err("No turnstile (⊢) found in goal".to_string());
        }

        Ok(ParsedGoal {
            hypotheses,
            proposition,
        })
    }

    /// Parse a JSON file containing proof data
    pub fn parse_json_file<P: AsRef<Path>>(path: P) -> Result<ProofData, String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read file: {}", e))?;
        
        serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse JSON: {}", e))
    }

    /// Extract all unique goals from a proof data structure
    pub fn extract_goals(proof_data: &ProofData) -> Vec<ParsedGoal> {
        let mut goals = Vec::new();
        let mut seen_goals = HashMap::new();

        for proof_step in &proof_data.proof_steps {
            if let Ok(parsed_goal) = Self::parse_goal(&proof_step.goals) {
                // Use the goal string as key to avoid duplicates
                if !seen_goals.contains_key(&proof_step.goals) {
                    seen_goals.insert(proof_step.goals.clone(), ());
                    goals.push(parsed_goal);
                }
            }
        }

        goals
    }

    /// Parse goals from a JSON file and return all unique goals
    pub fn parse_goals_from_file<P: AsRef<Path>>(path: P) -> Result<Vec<ParsedGoal>, String> {
        let proof_data = Self::parse_json_file(path)?;
        Ok(Self::extract_goals(&proof_data))
    }

    /// Get goals for a specific proof state
    pub fn get_goals_for_state(proof_data: &ProofData, state: u32) -> Vec<ParsedGoal> {
        proof_data.proof_steps
            .iter()
            .filter(|proof_step| proof_step.proof_state == state)
            .filter_map(|proof_step| Self::parse_goal(&proof_step.goals).ok())
            .collect()
    }

    /// Get all proof states and their corresponding goals
    pub fn get_all_states_with_goals(proof_data: &ProofData) -> HashMap<u32, Vec<ParsedGoal>> {
        let mut states = HashMap::new();
        
        for proof_step in &proof_data.proof_steps {
            if let Ok(parsed_goal) = Self::parse_goal(&proof_step.goals) {
                states.entry(proof_step.proof_state)
                    .or_insert_with(Vec::new)
                    .push(parsed_goal);
            }
        }

        states
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_goal() {
        let goal_str = "a b p : ℕ\nhp : Nat.Prime p\n⊢ p ∣ a * b → p ∣ a ∨ p ∣ b";
        let result = JsonParser::parse_goal(goal_str).unwrap();
        
        assert_eq!(result.hypotheses.len(), 2);
        assert_eq!(result.hypotheses[0].name, "a b p");
        assert_eq!(result.hypotheses[0].ty, "ℕ");
        assert_eq!(result.hypotheses[1].name, "hp");
        assert_eq!(result.hypotheses[1].ty, "Nat.Prime p");
        assert_eq!(result.proposition, "p ∣ a * b → p ∣ a ∨ p ∣ b");
    }

    #[test]
    fn test_parse_goal_with_multiple_hypotheses() {
        let goal_str = "a b p : ℕ\nhp : Nat.Prime p\nh : p ∣ a * b\n⊢ p ∣ a ∨ p ∣ b";
        let result = JsonParser::parse_goal(goal_str).unwrap();
        
        assert_eq!(result.hypotheses.len(), 3);
        assert_eq!(result.hypotheses[2].name, "h");
        assert_eq!(result.hypotheses[2].ty, "p ∣ a * b");
    }

    #[test]
    fn test_parse_goal_with_case() {
        let goal_str = "case inl\nn p : ℕ\nhp : Nat.Prime p\nh : p ∣ n * n\nh1 : p ∣ n\n⊢ p ∣ n";
        let result = JsonParser::parse_goal(goal_str).unwrap();
        
        assert_eq!(result.hypotheses.len(), 4);
        assert_eq!(result.proposition, "p ∣ n");
    }

    #[test]
    fn test_parse_empty_goal() {
        let result = JsonParser::parse_goal("");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_goal_without_turnstile() {
        let goal_str = "a b p : ℕ\nhp : Nat.Prime p";
        let result = JsonParser::parse_goal(goal_str);
        assert!(result.is_err());
    }
}
