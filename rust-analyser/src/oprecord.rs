//! OpRecord — one logical operation in a multi-agent history.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub type CellId = String;
pub type Value = String;
pub type AgentId = String;
pub type ToolId = String;
pub type Time = u64;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpRecord {
    pub agent: AgentId,
    pub read_set: Vec<CellId>,
    pub read_values: HashMap<CellId, Value>,
    pub read_time: Time,
    pub write_set: Vec<CellId>,
    pub write_values: HashMap<CellId, Value>,
    pub write_time: Time,
    #[serde(default)]
    pub planned_tool: Option<ToolId>,
    #[serde(default)]
    pub tools_used: Vec<ToolId>,
    #[serde(default)]
    pub tools_visible_at_read: Vec<ToolId>,
    #[serde(default)]
    pub io: Vec<(CellId, Value)>,
    #[serde(default)]
    pub co: Vec<(CellId, Value)>,
}

impl OpRecord {
    #[allow(dead_code)]
    pub fn reads(&self, c: &str) -> bool {
        self.read_set.iter().any(|x| x == c)
    }
    pub fn writes(&self, c: &str) -> bool {
        self.write_set.iter().any(|x| x == c)
    }
}

pub fn load_history(path: &std::path::Path) -> std::io::Result<Vec<OpRecord>> {
    use std::io::BufRead;
    let f = std::fs::File::open(path)?;
    let r = std::io::BufReader::new(f);
    let mut history = Vec::new();
    for line in r.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let op: OpRecord = serde_json::from_str(&line).map_err(|e| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, e.to_string())
        })?;
        history.push(op);
    }
    Ok(history)
}
