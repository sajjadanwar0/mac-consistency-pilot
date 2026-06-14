use crate::oprecord::{CellId, OpRecord, ToolId};

#[derive(Debug, Clone)]
pub struct Witness {
    pub i: usize,
    pub j: usize,
    pub cell: Option<CellId>,
    #[allow(dead_code)]
    pub tool: Option<ToolId>,
}

pub fn detect_a1(h: &[OpRecord]) -> Vec<Witness> {
    let mut out = Vec::new();
    for i in 0..h.len() {
        for j in 0..h.len() {
            if i == j {
                continue;
            }
            for c in &h[i].read_set {
                if !h[j].writes(c) {
                    continue;
                }
                if !(h[i].read_time < h[j].write_time
                    && h[j].write_time < h[i].write_time)
                {
                    continue;
                }
                let read_v = h[i].read_values.get(c);
                let write_v = h[j].write_values.get(c);
                if read_v != write_v {
                    out.push(Witness {
                        i,
                        j,
                        cell: Some(c.clone()),
                        tool: None,
                    });
                }
            }
        }
    }
    out
}

pub fn detect_a2(h: &[OpRecord]) -> Vec<Witness> {
    let mut out = Vec::new();
    for (i, op) in h.iter().enumerate() {
        let Some(planned) = &op.planned_tool else {
            continue;
        };
        let was_visible = op.tools_visible_at_read.iter().any(|t| t == planned);
        let was_used = op.tools_used.iter().any(|t| t == planned);
        if was_visible && !was_used {
            out.push(Witness {
                i,
                j: i,
                cell: None,
                tool: Some(planned.clone()),
            });
        }
    }
    out
}

pub fn detect_a3(h: &[OpRecord]) -> Vec<Witness> {
    let mut out = Vec::new();
    for (j, op) in h.iter().enumerate() {
        for c in &op.read_set {
            let read_v = match op.read_values.get(c) {
                Some(v) => v,
                None => continue,
            };
            if read_v == "NULL" {
                continue;
            }
            let has_antecedent = h.iter().enumerate().any(|(k, w)| {
                k != j
                    && w.writes(c)
                    && w.write_time <= op.read_time
                    && w.write_values.get(c) == Some(read_v)
            });
            if !has_antecedent {
                out.push(Witness {
                    i: j,
                    j,
                    cell: Some(c.clone()),
                    tool: None,
                });
            }
        }
    }
    out
}

pub fn detect_a6(h: &[OpRecord]) -> Vec<Witness> {
    let mut out = Vec::new();
    for (i, op) in h.iter().enumerate() {
        if op.io != op.co && !op.io.is_empty() {
            out.push(Witness {
                i,
                j: i,
                cell: None,
                tool: None,
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn op(
        agent: &str,
        rs: &[&str],
        rv: &[(&str, &str)],
        rt: u64,
        ws: &[&str],
        wv: &[(&str, &str)],
        wt: u64,
    ) -> OpRecord {
        OpRecord {
            agent: agent.into(),
            read_set: rs.iter().map(|s| s.to_string()).collect(),
            read_values: rv.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            read_time: rt,
            write_set: ws.iter().map(|s| s.to_string()).collect(),
            write_values: wv.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
            write_time: wt,
            planned_tool: None,
            tools_used: vec![],
            tools_visible_at_read: vec![],
            io: vec![],
            co: vec![],
        }
    }

    #[test]
    fn a1_canonical_witness() {
        let h = vec![
            op("a1", &["c1"], &[("c1", "NULL")], 0, &["c1"], &[("c1", "v1")], 2),
            op("a2", &["c1"], &[("c1", "NULL")], 0, &["c1"], &[("c1", "v2")], 1),
        ];
        let witnesses = detect_a1(&h);
        assert!(!witnesses.is_empty(), "expected A_1 witness");
    }

    #[test]
    fn a3_does_not_fire_on_simultaneous_write_and_read() {
        let h = vec![
            op("a1", &[], &[], 0, &["step"], &[("step", "start")], 1),
            op("a2", &["step"], &[("step", "start")], 1, &["step"], &[("step", "mid")], 2),
        ];
        assert!(detect_a3(&h).is_empty(), "A_3 should not fire here");
    }
}
