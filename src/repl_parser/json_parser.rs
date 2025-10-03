use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

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
#[derive(Debug, Clone, Serialize, Deserialize, Copy)]
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

    /// Parse a JSON file containing proof data
    pub fn parse_json_file<P: AsRef<Path>>(path: P) -> Result<ProofData, String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read file: {}", e))?;
        
        serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse JSON: {}", e))
    }
}