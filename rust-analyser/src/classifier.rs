//! Level classifier — find the maximum hierarchy level a history satisfies.
//!
//! Levels (paper §4):
//!   L_0 : TRUE          (admits everything)
//!   L_1 : ¬A_1
//!   L_2 : L_1 ∧ ¬A_3
//!   L_3 : L_2 ∧ ¬A_6
//!   L_4 : L_3 ∧ ¬A_2

use crate::anomalies::{detect_a1, detect_a2, detect_a3, detect_a6};
use crate::oprecord::OpRecord;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    L0,
    L1,
    L2,
    L3,
    L4,
}

impl Level {
    pub fn label(&self) -> &'static str {
        match self {
            Level::L0 => "L_0",
            Level::L1 => "L_1",
            Level::L2 => "L_2",
            Level::L3 => "L_3",
            Level::L4 => "L_4",
        }
    }
}

pub fn classify(h: &[OpRecord]) -> Level {
    if !detect_a1(h).is_empty() {
        return Level::L0;
    }
    if !detect_a3(h).is_empty() {
        return Level::L1;
    }
    if !detect_a6(h).is_empty() {
        return Level::L2;
    }
    if !detect_a2(h).is_empty() {
        return Level::L3;
    }
    Level::L4
}
